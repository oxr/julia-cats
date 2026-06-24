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

export Cat, DecidableCat, Func, NatTrans                                                    # types
export compose, check_unitl, check_unitr, check_assoc                                       # category laws
export func_comp, func_id, cat_cat                                                          # functoriality
export check_func_id, check_func_comp                                                       # functoriality laws
export check_naturality, nat_id, vcomp, hcomp_right, hcomp_left, hcomp                      # naturality laws
export check_vcomp_naturality, check_hcomp_right_naturality, check_hcomp_left_naturality    #
export check_interchange                                                                    #

# Categories without decidable equality on objects and morphisms
struct Cat
    dom  :: Function  # Mor -> Obj
    cod  :: Function  # Mor -> Obj
    id   :: Function  # Obj -> Mor
    comp :: Function  # Mor -> Mor -> Mor
end

# Categories with decidable equality on objects and morphisms
struct DecidableCat
    cat    :: Cat
    obj_eq :: Function  # Obj -> Obj -> Bool
    hom_eq :: Function  # Mor -> Mor -> Bool
end

# diagrammatic order composition
function compose(C::DecidableCat, f, g)
    @assert C.obj_eq(C.cat.cod(f), C.cat.dom(g)) "cod(f) != dom(g)"
    C.cat.comp(f, g)
end

# left unit law: id(dom(f)) ; f = f
function check_unitl(C::DecidableCat, f)
    C.hom_eq(compose(C, C.cat.id(C.cat.dom(f)), f), f)
end

# right unit law: f ; id(cod(f)) = f
function check_unitr(C::DecidableCat, f)
    C.hom_eq(compose(C, f, C.cat.id(C.cat.cod(f))), f)
end

# associativity law: (f ; g) ; h = f ; (g ; h)
function check_assoc(C::DecidableCat, f, g, h)
    C.hom_eq(
        compose(C, compose(C, f, g), h),
        compose(C, f, compose(C, g, h)))
end

## FUNCTORS
# Funtors F : C → D, where C and D are categories, act on objects and morphisms
struct Func
    dom     :: Cat
    cod     :: Cat
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
function func_id(C::Cat)
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
function check_func_id(F::Func, C::DecidableCat, D::DecidableCat, x)
    D.hom_eq(F.mor_map(C.cat.id(x)), D.cat.id(F.obj_map(x)))
end

# check that F(f ; g) = F(f) ; F(g)
function check_func_comp(F::Func, C::DecidableCat, D::DecidableCat, f, g)
    D.hom_eq(
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
function check_naturality(α::NatTrans, C::Cat, D::DecidableCat, f)
    x = C.dom(f)
    y = C.cod(f)
    D.hom_eq(
        compose(D, α.component(x), α.cod.mor_map(f)),
        compose(D, α.dom.mor_map(f), α.component(y)))
end

# identity natural transformation on F
function nat_id(F::Func)
    NatTrans(F, F, x -> F.cod.id(F.obj_map(x)))
end

# vertical composition: α : F ⇒ G, β : G ⇒ H  →  α;β : F ⇒ H
function vcomp(α::NatTrans, β::NatTrans, D::DecidableCat)
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
function check_vcomp_naturality(α::NatTrans, β::NatTrans, C::Cat, D::DecidableCat, f)
    check_naturality(vcomp(α, β, D), C, D, f)
end

# check naturality of right whiskering of a natural transformation
function check_hcomp_right_naturality(α::NatTrans, H::Func, C::Cat, E::DecidableCat, f)
    check_naturality(hcomp_right(α, H), C, E, f)
end

# check naturality of left whiskering of a natural transformation
function check_hcomp_left_naturality(H::Func, α::NatTrans, B::Cat, D::DecidableCat, f)
    check_naturality(hcomp_left(H, α), B, D, f)
end

# Godement product: α : F ⇒ G (C→D), γ : H ⇒ K (D→E)  →  H∘F ⇒ K∘G
# component at x: H(α_x) ; γ_{G(x)}
function hcomp(α::NatTrans, γ::NatTrans, E::DecidableCat)
    vcomp(hcomp_right(α, γ.dom), hcomp_left(α.cod, γ), E)
end

# interchange law: (α;β) * (γ;δ) = (α*γ) ; (β*δ)
# α,β : C→D vertically composable, γ,δ : D→E vertically composable
# checked pointwise at object x ∈ C
function check_interchange(α::NatTrans, β::NatTrans, γ::NatTrans, δ::NatTrans,
                            D::DecidableCat, E::DecidableCat, x)
    lhs = hcomp(vcomp(α, β, D), vcomp(γ, δ, E), E).component(x)
    rhs = vcomp(hcomp(α, γ, E), hcomp(β, δ, E), E).component(x)
    E.hom_eq(lhs, rhs)
end

end # module Cats
