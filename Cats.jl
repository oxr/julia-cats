# Cats.jl — core category theory primitives
#
# Defines the basic structures and laws of category theory:
#   Cat            — a category given by dom, cod, id, and comp functions
#   DecidableCat   — a Cat equipped with decidable equality on objects and morphisms,
#                    enabling runtime law checks (unit, associativity)
#   Func           — a functor between two Cats (object map + morphism map),
#                    with functoriality checks (preservation of id and comp)
#   NatTrans       — a natural transformation between two functors,
#                    with the naturality square check and vertical/horizontal composition
#
# All composition is in diagrammatic order (f then g, written f ; g).
# Decidability is kept separate from structure so constructions can be
# defined once on Cat and lifted to DecidableCat independently.

module Cats

export AbstractCat, AbstractDecidableCat, Cat, DecidableCat, Func, NatTrans                 # types
export dom, cod, id, comp, obj_eq, hom_eq                                                   # interface methods
export compose, check_unitl, check_unitr, check_assoc                                       # category laws
export func_comp, func_id, cat_cat                                                          # functoriality
export check_func_id, check_func_comp                                                       # functoriality laws
export check_naturality, nat_id, vcomp, hcomp_right, hcomp_left, hcomp                      # naturality laws
export check_vcomp_naturality, check_hcomp_right_naturality, check_hcomp_left_naturality    #
export check_interchange                                                                    #

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

## FUNCTORS
# Funtors F : C → D, where C and D are categories, act on objects and morphisms
struct Func
    dom     :: AbstractCat
    cod     :: AbstractCat
    obj_map :: Function  # dom.Obj -> cod.Obj
    mor_map :: Function  # dom.Mor -> cod.Mor
end

# Functor composition in diagrammatic order: F then G
function func_comp(F::Func, G::Func)
    @assert F.cod === G.dom "F.cod must be G.dom"
    Func(F.dom, G.cod,
         x -> G.obj_map(F.obj_map(x)),
         f -> G.mor_map(F.mor_map(f)))
end

# Identity functor on a category C
function func_id(C::AbstractCat)
    Func(C, C, x -> x, f -> f)
end

## category of categories, objects are categories, morphisms are functors
cat_cat = Cat(
    F -> F.dom,
    F -> F.cod,
    F -> func_id(F.dom),
    (F, G) -> func_comp(F, G)
)

## Functoriality checks
# check that F(id(x)) = id(F(x))
function check_func_id(F::Func, C::AbstractDecidableCat, D::AbstractDecidableCat, x)
    hom_eq(D, F.mor_map(id(C, x)), id(D, F.obj_map(x)))
end

# check that F(f ; g) = F(f) ; F(g)
function check_func_comp(F::Func, C::AbstractDecidableCat, D::AbstractDecidableCat, f, g)
    hom_eq(D,
        F.mor_map(compose(C, f, g)),
        compose(D, F.mor_map(f), F.mor_map(g)))
end

## NATURAL TRANSFORMATIONS
struct NatTrans
    dom :: Func            # F : C → D
    cod :: Func            # G : C → D
    component :: Function  # Obj(C) -> Mor(D),  x ↦ α_x : F(x) → G(x)
end

# naturality law: for f : x → y in C, α_y ; G(f) = F(f) ; α_x
function check_naturality(α::NatTrans, C::AbstractCat, D::AbstractDecidableCat, f)
    x = dom(C, f)
    y = cod(C, f)
    hom_eq(D,
        compose(D, α.component(x), α.cod.mor_map(f)),
        compose(D, α.dom.mor_map(f), α.component(y)))
end

# identity natural transformation on F
function nat_id(F::Func)
    NatTrans(F, F, x -> id(F.cod, F.obj_map(x)))
end

# vertical composition: α : F ⇒ G, β : G ⇒ H  →  α;β : F ⇒ H
function vcomp(α::NatTrans, β::NatTrans, D::AbstractCat)
    NatTrans(α.dom, β.cod,
             x -> compose(D, α.component(x), β.component(x)))
end

# whiskering on the right: α : F ⇒ G (C→D), H : D→E  →  H∘F ⇒ H∘G
function hcomp_right(α::NatTrans, H::Func)
    NatTrans(func_comp(α.dom, H), func_comp(α.cod, H),
             x -> H.mor_map(α.component(x)))
end

# whiskering on the left: H : B→C, α : F ⇒ G (C→D)  →  F∘H ⇒ G∘H
function hcomp_left(H::Func, α::NatTrans)
    NatTrans(func_comp(H, α.dom), func_comp(H, α.cod),
             x -> α.component(H.obj_map(x)))
end

# check naturality of vertical composition of natural transformations
function check_vcomp_naturality(α::NatTrans, β::NatTrans, C::AbstractCat, D::AbstractDecidableCat, f)
    check_naturality(vcomp(α, β, D), C, D, f)
end

# check naturality of right whiskering of a natural transformation
function check_hcomp_right_naturality(α::NatTrans, H::Func, C::AbstractCat, E::AbstractDecidableCat, f)
    check_naturality(hcomp_right(α, H), C, E, f)
end

# check naturality of left whiskering of a natural transformation
function check_hcomp_left_naturality(H::Func, α::NatTrans, B::AbstractCat, D::AbstractDecidableCat, f)
    check_naturality(hcomp_left(H, α), B, D, f)
end

# Godement product: α : F ⇒ G (C→D), γ : H ⇒ K (D→E)  →  H∘F ⇒ K∘G
# component at x: H(α_x) ; γ_{G(x)}
function hcomp(α::NatTrans, γ::NatTrans, E::AbstractCat)
    vcomp(hcomp_right(α, γ.dom), hcomp_left(α.cod, γ), E)
end

# interchange law: (α;β) * (γ;δ) = (α*γ) ; (β*δ)
# α,β : C→D vertically composable, γ,δ : D→E vertically composable
# checked pointwise at object x ∈ C
function check_interchange(α::NatTrans, β::NatTrans, γ::NatTrans, δ::NatTrans,
                            D::AbstractDecidableCat, E::AbstractDecidableCat, x)
    lhs = hcomp(vcomp(α, β, D), vcomp(γ, δ, E), E).component(x)
    rhs = vcomp(hcomp(α, γ, E), hcomp(β, δ, E), E).component(x)
    hom_eq(E, lhs, rhs)
end

end # module Cats
