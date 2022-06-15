# In this file, I began to write something, that would give me a 
# type intersection for A<:B whilst keeping the type variables of B.
# This turned out harder than I thought at first.
# It seems, that it would require a re-implementation of `scr/subtype.c`
# in Julia and I am in no way qualified to do that.

# src/subtype.c
import Base: Bottom
import Base: unwrap_unionall

const TUPLE_TYPENAME = Tuple.name # `jl_tuple_typename`?
# const TUPLE_TYPENAME = unsafe_load( unsafe_load( cglobal(:jl_tuple_typename, Ptr{Core.TypeName} ) ) )

# src/julia.h
# jl_is_tuple_type
_is_tuple_type(T) = false 
_is_tuple_type(T :: DataType) = T.name == TUPLE_TYPENAME

# src/julia_internal.h
# `jl_is_va_tuple`
_is_va_tuple(T) = false
function _is_va_tuple(T :: DataType)
	@assert _is_tuple_type(T)
	l = length(T.parameters)
	return l > 0 && T.parameters[l-1] isa Core.TypeofVararg
end
# `jl_is_type_type`
_is_type_type(T) = false
function _is_type_type(dt :: DataType)
	return dt.name == dt.body.name
end

# src/subtype.c
# Julia implementation of `obviously_disjoint`
function obviously_disjoint(A::Type, B::Type, specificity = false) :: Bool
	if A == B || A == Any || B == Any
		return false
	end
	if specificity && A == Bottom
		return false
	end
	if (
		isconcretetype(A) && isconcretetype(B) &&
		ccall(:jl_type_equality_is_identity, Cint, (Any, Any), A, B) &&
		( A.name != TUPLE_TYPENAME || B..name != TUPLE_TYPENAME )
	)
		return true
	end
	a = A isa UnionAll ? unwrap_unionall(A) : A
	b = B isa UnionAll ? unwrap_unionall(B) : B
	if a isa DataType && b isa DataType
		if a.name != b.name
			temp = a
			while temp != Any && temp.name != b.name
				temp = temp.super
			end
			if temp == Any
				temp = b
				while temp != Any && temp.name != a.name
					temp = temp.super
				end
				if temp == Any 
					return true
				end
				b = temp
			else
				a = temp
			end
			if specificity
				return false
			end
		end # a.name != b.name
		# now a.name == b.name
		istuple = a.name == TUPLE_TYPENAME
		np = if istuple
			na = length(a.parameters)
			nb = length(b.parameters)
			if _is_va_tuple(a)
				na -= 1
				if _is_va_tuple(b)
					nb -= 1
				end
			elseif _is_va_tuple(b)
				nb -= 1
			elseif !specificity && na != nb
				return true
			end
			min( na, nb )
		else
			length( a.parameters )
		end# istuple

		for i=1:np
			ai = a.parameters[i]
			bi = b.parameters[i]
			(ai isa TypeVar || bi isa TypeVar) && continue
			
			if ai isa Type
				if bi isa Type
					if (
						!(istuple && (ai == Bottom || bi == Bottom)) &&
						obviously_disjoint(ai, bi, specificity)
					)
						return true
					end
				elseif ai != Any
					return true
				end
			elseif bi isa Type
				if bi != Any
					return true
				end
			elseif !(ai === bi)
				return true
			end
		end#for
	elseif a == Bottom || b == Bottom
		return true
	end # a isa DataType && b isa DataType
	return false
end# function

might_intersect_concrete( :: Any ) = false
might_intersect_concrete( :: TypeVar ) = true
function might_intersect_concrete( :: Vararg{T} ) where T
	return might_intersect_concrete(T)
end
function might_intersect_concrete( :: Vararg{T,N} ) where {T,N}
	return might_intersect_concrete(T)
end
function might_intersect_concrete( A :: UnionAll ) 
	might_intersect_concrete( Base.unwrap_unionall( A ) )
end
function might_intersect_concrete( U :: Union )
	return might_intersect_concrete(U.a) ||
		might_intersect_concrete(U.b)
end
function might_intersect_concrete( dt :: DataType )
	if _is_type_type(dt)
		return true
	end
	tpl = _is_tuple_type( dt )
	for p in dt.parameters
		if p isa TypeVar
			return true
		end
		if tpl && p == Bottom
			return true
		end
		if tpl && might_intersect_concrete(p)
			return true
		end
	end
	return false
end

# src/subtype.c

Base.@kwdef struct STEnv
	vars :: Vector{TypeVar}
	Lunions 
	Runions
	envout 
	envsz :: Int
	envidx :: Int = 1               # current index in envout
    invdepth :: Int = 0            # # of invariant constructors we're nested in on the left
    Rinvdepth :: Int = 0            # # of invariant constructors we're nested in on the right
    ignore_free :: Bool = false         # treat free vars as black boxes; used during intersection
    intersection :: Bool = false         # true iff subtype is being called from intersection
    emptiness_only :: Bool = false      # true iff intersection only needs to test for emptiness
    triangular :: Bool = false         # when intersecting Ref{X} with Ref{<:Y}
end


# `jl_type_intersection_env_s`
function _type_intersection(A :: Type, B :: Type)
	A_subtypes_B = false
	
	if obviously_disjoint(A, B)
		if A == Bottom 
			A_subtypes_B = true
		end
		return Bottom
	end
	# length of UnionAll-Chain:
	szb = ccall(:jl_subtype_env_size, Cint, (Any,), B)
	sz = 0
	i = 0

	ans = Bottom
	env = [Vector{Any}(undef, szb); ans]
	
	lta = isconcretetype(A)
	ltb = isconcretetype(B)
	@show ccall(:jl_subtype_env, Cint, (Any, Any, Array{Any}, Cint), A, B, env, szb) 
	if isone( ccall(:jl_subtype_env, Cint, (Any, Any, Array{Any}, Cint), A, B, env, szb) )
		ans = A
		sz = szb
		A_subtypes_B = true
	elseif lta && ltb
		@goto bot
	elseif B <: A
		ans = B
	else
		if lta && !might_intersect_concrete(B)
			@goto bot
		end
		if ltb && !might_intersect_concrete(A)
			@goto bot
		end
		# todo
	end
	

	@label bot
	return ans
end

# taken from 
# `_subtypes_in!` in file
# `stdlib/InteractiveUtils.jl`
import InteractiveUtils: isdeprecated
function _subtypes_in!(mods::Array, x::Type)
    xt = unwrap_unionall(x)
    if !isabstracttype(x) || !isa(xt, DataType)
        # Fast path
        return Type[]
    end
    sts = Vector{Any}()
    while !isempty(mods)
        m = pop!(mods)
        xt = xt::DataType
        for s in names(m, all = true)
            if isdefined(m, s) && !isdeprecated(m, s)
                t = getfield(m, s)
                dt = isa(t, UnionAll) ? unwrap_unionall(t) : t
                if isa(dt, DataType)
                    if dt.name.name === s && dt.name.module == m && supertype(dt).name == xt.name
                        ti = typeintersect(t, x)
                        ti != Bottom && push!(sts, ti)
                    end
                elseif isa(t, Module) && nameof(t) === s && parentmodule(t) === m && t !== m
                    t === Base || push!(mods, t) # exclude Base, since it also parented by Main
                end
            end
        end
    end
    return permute!(sts, sortperm(map(string, sts)))
end