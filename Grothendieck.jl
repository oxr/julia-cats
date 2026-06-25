# Grothendieck.jl — Set-valued functors via the Grothendieck construction
#
# Representing functors F : C → Set directly requires Set to exist as a
# category, which needs universes or class theory. Instead, we encode F
# by its Grothendieck total category E and the projection π : E → C.
#
#   SetFunctor       — concrete representation of F : C → Set (obj_map and
#                      mor_map as Julia functions, no Set-as-category needed)
#   GObj / GMor      — objects (a, x) and morphisms (h, x, y) of the total
#                      category E; morphisms box the base C-morphism h together
#                      with its fiber endpoints so dom/cod return the full pair
#   grothendieck     — builds the total Cat (or DecidableCat) from a SetFunctor
#   groth_proj       — the projection functor π : E → C
#   DiscreteFibration — packages (E, C, π) together; equivalent to a Set-valued
#                       functor on C by the Grothendieck correspondence
#   FibMor           — morphism of fibrations (= natural transformation F ⇒ G):
#                      a functor Φ : E → E' commuting with the projections

module Grothendieck

using ..Cats

export SetFunctor, GObj, GMor, grothendieck, groth_proj
export DiscreteFibration, discrete_fibration, in_fiber
export FibMor, check_fibmor_obj, check_fibmor_mor, fib_id, fib_comp

struct SetFunctor
    dom     :: AbstractCat
    obj_map :: Function   # Obj(C) → collection
    mor_map :: Function   # Mor(C) → Function (between collections)
end

struct GObj
    base  :: Any   # a : Obj(C)
    fiber :: Any   # x : F(a)
end

struct GMor
    dom :: GObj   # (a, x)
    cod :: GObj   # (b, y)
    mor :: Any    # h : a → b in C
end

# Grothendieck construction: total category E from F : C → Set
function grothendieck(F::SetFunctor)
    C = F.dom
    Cat(
        gm -> gm.dom,
        gm -> gm.cod,
        go -> GMor(go, go, id(C, go.base)),
        (gm1, gm2) -> GMor(gm1.dom, gm2.cod, comp(C, gm1.mor, gm2.mor))
    )
end

# DecidableCat on E: fiber_eq compares elements within a fiber
function grothendieck(F::SetFunctor, C::DecidableCat, fiber_eq::Function)
    DecidableCat(
        grothendieck(F),
        (go1, go2) -> obj_eq(C, go1.base, go2.base) && fiber_eq(go1.fiber, go2.fiber),
        (gm1, gm2) -> hom_eq(C, gm1.mor, gm2.mor)
    )
end

# Projection functor π : E → C
function groth_proj(F::SetFunctor)
    Func(grothendieck(F), F.dom,
         go -> go.base,
         gm -> gm.mor)
end

# A discrete fibration over C, equivalent to a Set-valued functor on C
struct DiscreteFibration
    total :: AbstractCat
    base  :: AbstractCat
    proj  :: Func
end

discrete_fibration(F::SetFunctor) = DiscreteFibration(grothendieck(F), F.dom, groth_proj(F))

in_fiber(DC::DecidableCat, go::GObj, a) = DC.obj_eq(go.base, a)

# Morphism of fibrations = nat trans F ⇒ G: functor Φ : E → E' with π' ∘ Φ = π
struct FibMor
    dom :: DiscreteFibration
    cod :: DiscreteFibration
    map :: Func
end

function check_fibmor_obj(fm::FibMor, DC::AbstractDecidableCat, go::GObj)
    obj_eq(DC,
        fm.cod.proj.obj_map(fm.map.obj_map(go)),
        fm.dom.proj.obj_map(go))
end

function check_fibmor_mor(fm::FibMor, DC::AbstractDecidableCat, gm::GMor)
    hom_eq(DC,
        fm.cod.proj.mor_map(fm.map.mor_map(gm)),
        fm.dom.proj.mor_map(gm))
end

fib_id(df::DiscreteFibration)       = FibMor(df, df, func_id(df.total))
fib_comp(fm1::FibMor, fm2::FibMor) = FibMor(fm1.dom, fm2.cod, func_comp(fm1.map, fm2.map))

end # module Grothendieck
