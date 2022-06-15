module SimilarType

using InteractiveUtils: subtypes

export similar_array_type

@generated function similar_array_type( _T :: Type{<:AbstractArray}, _F :: Type{<:Number} )
    T = _unwrap_type(_T)
    F = _unwrap_type(_F)
    _T = _similar_array_type( T, F )
    return quote $(_T) end
end

function _chnl( elem :: T ) where T
    chnl = Channel{T}(1)
    put!(chnl, elem)
    close(chnl)
    return chnl
end

function possible_types( :: Core.TypeofBottom )
   return _chnl(Base.Bottom)
end

function possible_types( dt :: DataType )
   return _chnl(dt)
end

function possible_types( u :: Union )
    chnl = Channel()
    Base.Experimental.@async begin
        for pt in possible_types(u.a)
            put!(chnl, pt)
        end
        for pt in possible_types(u.b)
            put!(chnl, pt)
        end
    end
    return chnl
end

function possible_types( u :: UnionAll )
    chnl = Channel()

    Base.Experimental.@async begin
        for pt in possible_types(u.var)
            put!( chnl, x{pt})
        end
        close(chnl)
    end
    return chnl
end

_supertype( u ) = supertype(u)
function _supertype( u :: Union )
    u.a == Base.Bottom && return _supertype(u.b)
    u.b == Base.Bottom && return _supertype(u.a)
    
    sa = _supertype(u.a)
    sa == Any && return Any
    sb = _supertype(u.b)
    sb == Any && return Any
    if sa != sb
        # go one level up:
        return _supertype( Union{sa,sb} )
    else
        return sa
    end
end

function _all_types(T = Any, c = Channel())
    Base.Experimental.@async begin
        for S in subtypes(T)
            put!(c, S)
            _all_types(S,c)
        end
        close(c)
    end
    return c
end      

function possible_types( tv :: TypeVar )
    if tv.lb == tv.ub
        return _chnl( tv.lb )
    end
    if tv.lb == Base.Bottom && tv.ub == Any
        return _all_types()
    end

    c = Channel()
    ct = possible_types_task( tv, c ) 
    bind(c, ct)
    return c
end

function possible_types_task( tv :: TypeVar, c :: Channel)
    if tv.lb == tv.ub
        return @async put!(c, tv.lb )
    end

    if tv.lb != Base.Bottom
        # step up from tv.lb ( != Base.Bottom )
        channel_task = Base.Experimental.@async begin
            supers = Any[]
            for pt in possible_types(tv.lb)
                put!(c, pt )
                spt = _supertype(pt)    # possible bc of `pt != Base.Bottom`
                if !(spt in supers)
                    push!(supers, spt)
                    Base.Experimental.wait(possible_types_task( TypeVar( gensym(), spt , tv.ub ), c ))
                end                   
            end
        end# async
    else
        # step down from tv.ub != Any
        channel_task = Base.Experimental.@async begin
            subs = Set()
            for pt in possible_types(tv.ub)
                put!(c, pt)
                subs_pt = setdiff( subtypes( pt ), subs )
                if !(isempty(subs_pt))
                    union!(subs, subs_pt)
                    for spt in subs_pt
                        Base.Experimental.wait( possible_types_task( TypeVar( gensym(), tv.lb , spt ), c ) )
                    end
                end                    
            end
        end# async        
    end
    return channel_task
end

_unwrap_type( :: Type{Type{F}} ) where F = F

function _similar_array_type( T :: Type{<:AbstractArray{<:Number, N}}, F :: Type{<:Number}) where N
    _T = _similar_type( 
        T,
        TypeVar( gensym(), AbstractArray{F, N} )    
    )
    if _T == Base.Bottom
        return _fallback( T, F )
    else
        return _T
    end
end

function _fallback( :: Type{<:AbstractArray{<:Number, N}}, F :: Type{<:Number} ) where N
	return Array{F, N}
end

function _set_type_var_in_R_and_T( R, T, leaf_params, T_wrapper, j, p; do_checks = true )    
    num_params = length(leaf_params)
    _p = leaf_params[j]

    R = R{p}

    _T = if p != _p && do_checks
        # instantiating `R{p}` might change stuff down in the `UnionAll` chain:
        # if `R.var` was a TypeVar before, and it appeared in the bounds of 
        # subsequent type variables, then
        # a) the bounds of subsequent type variables in `T` might need to be changed
        # b) we should probably check type variable values againts new bounds (?)
        # Thus we update T & T_leaf:
        # 1) We use the first `j` variable values as set for `R`
        # 2) We then retry to use the other values of `T_leaf`.
        #    The bounds are checked in `_similar_type(P, T.var)`.
        R_leaf = Base.unwrap_unionall( R )
        R_leaf_params = R_leaf.parameters
        __T = T_wrapper
        i = 1 
        for i=1:j-1
            __T = __T{ leaf_params[i] }
        end
        __T = __T{p}
        for i=j+1:length(leaf_params)
            _P = leaf_params[i]
            Q = R_leaf_params[i] :: TypeVar
            if _P isa TypeVar 
                lb = typeintersect( _P.lb, Q.lb )
                ub = typeintersect( _P.ub, Q.ub )
                if (!(lb <: ub) || ub == Base.Bottom) 
                    __T = Base.Bottom
                    break
                end
                P = TypeVar(_P.name, lb, ub )
            else
                if _P isa Type && !( Q.lb <: _P <: Q.ub )
                    __T = Base.Bottom
                    break
                end
                P = _P
            end
            __T = __T{P}
        end#for 
        __T
    else
        T
    end
    return R, _T
end

function _loop_and_set( IN_Type, T, T_wrapper )
    @assert Base.typename(T) == IN_Type.name

    R = T_wrapper
    j = 1
    while R isa UnionAll
        leaf_params = Base.unwrap_unionall(T).parameters
        _p = leaf_params[j]
        p = if _p isa TypeVar
            q = IN_Type.parameters[j]
            _similar_type( q, _p )
        else
            _p
        end
        p == Base.Bottom && return p 
        if p isa TypeVar
            @show p
            for pt in possible_types(p)
                @show pt
                R, T = _set_type_var_in_R_and_T(R, T, leaf_params, T_wrapper, j, pt)
                @show Base.unwrap_unionall(T).parameters
                T == Base.Bottom && continue
                _R = _loop_and_set(IN_Type, T, T_wrapper )
                _R != Base.Bottom && return _R
            end
            return Base.Bottom
        else
            R, T = _set_type_var_in_R_and_T(R, T, leaf_params, T_wrapper, j, p; do_checks = j < length(leaf_params))
            T == Base.Bottom && return T
        end  
        j += 1
    end # while R isa UnionAll
    return R
end

function _similar_type( IN_Type, TARGET :: TypeVar )
    @show IN_Type, TARGET

    # very quick and easy checks for early return:
    if IN_Type isa Type
        if TARGET.lb <: IN_Type <: TARGET.ub
            return IN_Type
        end
    else
        if !(IN_Type isa TypeVar)
            return IN_Type
        end
    end

    if IN_Type isa DataType
        IN_wrapper = IN_Type.name.wrapper
        if IN_wrapper isa UnionAll
            T = typeintersect( IN_wrapper, TARGET )
            if T isa DataType
                return T # might be Bottom
            elseif T isa UnionAll
                return _loop_and_set(IN_Type, T, IN_wrapper )
            end # T isa UnionAll
        else
            # e.g.: T = AbstractFloat
            # TARGET = Int <: S <: Any => allows for S in {Int, Signed, Integer, …}
            # but for some reason typeintersect does not work as expected:
            # `typeintersect( Type{AbstractFloat}, Type{T} where T>:Int ) == Union{}` ✓
            # `typeintersect( AbstractFloat, TypeVar( gensym, Int, Any) ) == AbstractFloat` ❎
            _T = typeintersect( Type{IN_wrapper}, UnionAll( TARGET, Type{TARGET}) )
            if _T == Base.Bottom
                return TARGET
            end
            return _unwrap_type(T)
        end# IN_wrapper isa UnionAll
    end # IN_Type isa DataType

    # `IN_Type` is not a DataType but a Type that does not satisfy the bounds:
    return Base.Bottom
end # function

end # module
