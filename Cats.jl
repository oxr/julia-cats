# Cats.jl — core category theory primitives
#
# Defines the fundamental structures of category theory:
#   Cat          — a category given by dom, cod, id, and comp functions
#   DecidableCat — a Cat equipped with decidable equality on objects and morphisms,
#                  enabling runtime law checks (unit, associativity)
#
# Functors and natural transformations live in Functors.jl.
#
# All composition is in diagrammatic order (f then g, written f ; g).
# Decidability is kept separate from structure so constructions can be
# defined once on Cat and lifted to DecidableCat independently.

module Cats

export AbstractCat, AbstractDecidableCat, Cat, DecidableCat   # types
export dom, cod, id, comp, obj_eq, hom_eq                     # interface methods
export compose, check_unitl, check_unitr, check_assoc         # category laws

abstract type AbstractCat end
abstract type AbstractDecidableCat <: AbstractCat end

# Categories without decidable equality on objects and morphisms
struct Cat <: AbstractCat
    dom  :: Function  # Mor -> Obj
    cod  :: Function  # Mor -> Obj
    id   :: Function  # Obj -> Mor
    comp :: Function  # Mor -> Mor -> Mor
end

dom(C::Cat, f) = C.dom(f)
cod(C::Cat, f) = C.cod(f)
id(C::Cat, x) = C.id(x)
comp(C::Cat, f, g) = C.comp(f, g)

# Categories with decidable equality on objects and morphisms
struct DecidableCat <: AbstractDecidableCat
    cat    :: Cat
    obj_eq :: Function  # Obj -> Obj -> Bool
    hom_eq :: Function  # Mor -> Mor -> Bool
end

dom(C::DecidableCat, f) = C.cat.dom(f)
cod(C::DecidableCat, f) = C.cat.cod(f)
id(C::DecidableCat, x) = C.cat.id(x)
comp(C::DecidableCat, f, g) = C.cat.comp(f, g)
obj_eq(C::DecidableCat, a, b) = C.obj_eq(a, b)
hom_eq(C::DecidableCat, f, g) = C.hom_eq(f, g)

# diagrammatic order composition
function compose(C::AbstractCat, f, g)
    comp(C, f, g)
end

function compose(C::AbstractDecidableCat, f, g)
    @assert obj_eq(C, cod(C, f), dom(C, g)) "cod(f) != dom(g)"
    comp(C, f, g)
end

# left unit law: id(dom(f)) ; f = f
function check_unitl(C::AbstractDecidableCat, f)
    hom_eq(C, compose(C, id(C, dom(C, f)), f), f)
end

# right unit law: f ; id(cod(f)) = f
function check_unitr(C::AbstractDecidableCat, f)
    hom_eq(C, compose(C, f, id(C, cod(C, f))), f)
end

# associativity law: (f ; g) ; h = f ; (g ; h)
function check_assoc(C::AbstractDecidableCat, f, g, h)
    hom_eq(C,
        compose(C, compose(C, f, g), h),
        compose(C, f, compose(C, g, h)))
end

end # module Cats
