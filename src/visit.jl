# Thread-safe file logging for debugging
const _debug_log_dir = Ref{String}("")
const _debug_log_files = Dict{Int, IOStream}()
const _debug_log_lock = ReentrantLock()

function _init_debug_logging()
    if isempty(_debug_log_dir[])
        _debug_log_dir[] = mktempdir(prefix="revise_debug_")
        @info "Revise debug logs will be written to: $(_debug_log_dir[])"
    end
end

function _debug_log(msg::String)
    tid = Threads.threadid()
    @info "[REVISE DEBUG] _debug_log called: tid=$tid msg=$msg"
    @lock _debug_log_lock begin
        _init_debug_logging()
        if !haskey(_debug_log_files, tid)
            filepath = joinpath(_debug_log_dir[], "thread_$(tid).log")
            _debug_log_files[tid] = open(filepath, "w")
        end
        io = _debug_log_files[tid]
        t = round(time(), digits=3)
        println(io, "[$t] $msg")
        flush(io)
    end
end

function _close_debug_logs()
    @lock _debug_log_lock begin
        for (tid, io) in _debug_log_files
            close(io)
        end
        empty!(_debug_log_files)
    end
end

#     old_methods_with(oldtypename::Core.TypeName) -> Union{Nothing, Set{Method}}
#
# Find all methods whose signature references `oldtypename`.
#
# When a type is redefined, methods that reference the old type in their signature
# need to be re-evaluated. This function traverses the global method table and
# collects all methods that have `oldtypename` in any of their signature parameters.
#
# For example, if `OldType` is being redefined and there exists a method
# `foo(x::OldType)`, that method will be included in the returned set.
#
# See also [`old_types_with`](@ref).
function old_methods_with(oldtypename::Core.TypeName)
    _debug_log("old_methods_with called: mod=$(oldtypename.module) name=$(oldtypename.name)")
    meths = nothing
    methodtable = @static isdefinedglobal(Core, :methodtable) ? Core.methodtable : Core.GlobalMethods
    method_count = 0
    match_count = 0
    Base.visit(methodtable) do method
        method_count += 1
        if method_count % 10000 == 0
            _debug_log("old_methods_with progress: method_count=$method_count match_count=$match_count")
        end
        sigt = Base.unwrap_unionall(method.sig)
        if sigt isa DataType
            for i = 1:length(sigt.parameters)
                if is_with_oldtypename(sigt.parameters[i], oldtypename)
                    if meths === nothing
                        meths = Set{Method}()
                    end
                    push!(meths, method)
                    match_count += 1
                    break
                end
            end
        end
    end
    _debug_log("old_methods_with finished: total_methods=$method_count match_count=$match_count")
    return meths
end

const _collect_subtypes_depth = Ref(0)

function collect_all_subtypes(@nospecialize(parent_typ::Type))
    _debug_log("collect_all_subtypes called: parent_typ=$parent_typ")
    _collect_subtypes_depth[] = 0
    result = _foreach_subtype!(Returns(nothing), parent_typ, Base.IdSet{Type}())
    _debug_log("collect_all_subtypes finished: parent_typ=$parent_typ result_count=$(length(result))")
    return result
end

function foreach_subtype(f::Function, @nospecialize(parent_typ::Type))
    _debug_log("foreach_subtype called (likely background thread): parent_typ=$parent_typ")
    _foreach_subtype!(f, parent_typ, Base.IdSet{Type}())
    _debug_log("foreach_subtype finished: parent_typ=$parent_typ")
    return nothing
end

function _foreach_subtype!(f::Function, @nospecialize(parent_typ::Type), types::Base.IdSet{Type})
    _collect_subtypes_depth[] += 1
    depth = _collect_subtypes_depth[]
    
    if depth > 100
        _debug_log("_foreach_subtype! MAX DEPTH EXCEEDED: depth=$depth parent_typ=$parent_typ")
        _collect_subtypes_depth[] -= 1
        return types
    end
    
    if depth <= 5 || depth % 20 == 0
        _debug_log("_foreach_subtype!: depth=$depth parent_typ=$parent_typ types_count=$(length(types))")
    end
    
    subtypes_list = InteractiveUtils.subtypes(parent_typ)
    for (idx, Ty) in enumerate(subtypes_list)
        if Ty in types
            continue
        else
            f(Ty)
            push!(types, Ty)
            _foreach_subtype!(f, Ty, types)
        end
    end
    _collect_subtypes_depth[] -= 1
    return types
end

# TODO Use fixed sized FIFO cache?
const types_cache = IdDict{Type,Union{Nothing,Vector{Any}}}()
const types_cache_lock = ReentrantLock()
const _fieldtypes_cached_count = Ref(0)

function fieldtypes_cached(@nospecialize(type))
    _fieldtypes_cached_count[] += 1
    count = _fieldtypes_cached_count[]
    # Log every 5000 calls to avoid flooding
    if count % 5000 == 0
        _debug_log("fieldtypes_cached progress: call_count=$count cache_size=$(length(types_cache))")
    end
    # This function is called from the cache thread during __init__ so we need the lock here
    @lock types_cache_lock begin
        return get!(types_cache, type) do
            nflds = Base.Compiler.fieldcount_noerror(type)
            if nflds !== nothing && nflds > 0
                ftypes = collect(Any, fieldtypes(type))
            else
                ftypes = nothing
            end
            ftypes
        end
    end
end

#     old_types_with(oldtypename::Core.TypeName, alltypes::Base.IdSet{Type}) -> Union{Nothing, Base.IdSet{Type}}
#
# Find all types whose field types reference `oldtypename`.
#
# When a type is redefined, other types that use it as a field type also need to
# be re-evaluated. This function traverses all known types and collects those that
# have `oldtypename` in any of their field types.
#
# For example, if `Inner` is being redefined and there exists
# `struct Outer; x::Inner; end`, then `Outer` will be included in the returned set.
#
# See also [`old_methods_with`](@ref).
function old_types_with(oldtypename::Core.TypeName, alltypes::Base.IdSet{Type})
    _debug_log("old_types_with called: mod=$(oldtypename.module) name=$(oldtypename.name) alltypes_count=$(length(alltypes))")
    related_types = nothing
    type_count = 0
    match_count = 0
    for type in alltypes
        type_count += 1
        if type_count % 5000 == 0
            _debug_log("old_types_with progress: type_count=$type_count match_count=$match_count")
        end
        types = fieldtypes_cached(type)
        if types !== nothing
            for ft in types
                if is_with_oldtypename(ft, oldtypename)
                    if related_types === nothing
                        related_types = Base.IdSet{Type}()
                    end
                    push!(related_types, type)
                    match_count += 1
                    break
                end
            end
        end
    end
    _debug_log("old_types_with finished: total_types=$type_count match_count=$match_count")
    return related_types
end

function is_with_oldtypename(@nospecialize(typlike), oldtypename::Core.TypeName)
    if typlike isa DataType
        typlike.name == oldtypename && return true
        for i = 1:length(typlike.parameters)
            if is_with_oldtypename(typlike.parameters[i], oldtypename)
                return true
            end
        end
    elseif typlike isa UnionAll
        return is_with_oldtypename(typlike.body, oldtypename)
    elseif typlike isa TypeVar
        return is_with_oldtypename(typlike.lb, oldtypename) || is_with_oldtypename(typlike.ub, oldtypename)
    end
    return false
end
