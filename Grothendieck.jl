include("Cats.jl")
using .Cats

# A Set-valued functor F : C → Set, represented concretely in Julia.
# Avoids needing Set as a category object — instead we build the total
# category via the Grothendieck construction and work with fibrations.
struct SetFunctor
    dom     :: Cat
    obj_map :: Function   # Obj(C) → collection
    mor_map :: Function   # Mor(C) → Function (between collections)
end

# Objects and morphisms of the Grothendieck total category E
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
# objects: pairs (a, x),  morphisms: (h : a→b in C, with F(h)(x) = y)
function grothendieck(F::SetFunctor)
    C = F.dom
    Cat(
        gm -> gm.dom,
        gm -> gm.cod,
        go -> GMor(go, go, C.id(go.base)),
        (gm1, gm2) -> GMor(gm1.dom, gm2.cod, C.comp(gm1.mor, gm2.mor))
    )
end

# DecidableCat on E: fiber_eq compares elements within a fiber
function grothendieck(F::SetFunctor, C::DecidableCat, fiber_eq::Function)
    DecidableCat(
        grothendieck(F),
        (go1, go2) -> C.obj_eq(go1.base, go2.base) && fiber_eq(go1.fiber, go2.fiber),
        (gm1, gm2) -> C.hom_eq(gm1.mor, gm2.mor)
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
    total :: Cat
    base  :: Cat
    proj  :: Func   # π : total → base
end

function discrete_fibration(F::SetFunctor)
    DiscreteFibration(grothendieck(F), F.dom, groth_proj(F))
end

# Check that go lives in the fiber over a
in_fiber(DC::DecidableCat, go::GObj, a) = DC.obj_eq(go.base, a)

# Morphism of discrete fibrations = natural transformation F ⇒ G
# A functor Φ : E → E' that commutes with the projections: π' ∘ Φ = π
struct FibMor
    dom :: DiscreteFibration
    cod :: DiscreteFibration
    map :: Func               # Φ : E → E'
end

function check_fibmor_obj(fm::FibMor, DC::DecidableCat, go::GObj)
    DC.obj_eq(
        fm.cod.proj.obj_map(fm.map.obj_map(go)),
        fm.dom.proj.obj_map(go))
end

function check_fibmor_mor(fm::FibMor, DC::DecidableCat, gm::GMor)
    DC.hom_eq(
        fm.cod.proj.mor_map(fm.map.mor_map(gm)),
        fm.dom.proj.mor_map(gm))
end

fib_id(df::DiscreteFibration)              = FibMor(df, df, func_id(df.total))
fib_comp(fm1::FibMor, fm2::FibMor)        = FibMor(fm1.dom, fm2.cod, func_comp(fm1.map, fm2.map))

