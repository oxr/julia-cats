struct Cat
    dom  :: Function  # Mor -> Obj
    cod  :: Function  # Mor -> Obj
    id   :: Function  # Obj -> Mor
    comp :: Function  # Mor -> Mor -> Mor
end

struct Func
    dom     :: Cat
    cod     :: Cat
    obj_map :: Function  # dom.Obj -> cod.Obj
    mor_map :: Function  # dom.Mor -> cod.Mor
end

struct DecidableCat
    cat    :: Cat
    obj_eq :: Function  # Obj -> Obj -> Bool
    hom_eq :: Function  # Mor -> Mor -> Bool
end

# diagrammatic order
function compose(C::DecidableCat, f, g)
    @assert C.obj_eq(C.cat.cod(f), C.cat.dom(g)) "cod(f) != dom(g)"
    C.cat.comp(f, g)
end

function check_unitl(C::DecidableCat, f)
    C.hom_eq(compose(C, C.cat.id(C.cat.dom(f)), f), f)
end

function check_unitr(C::DecidableCat, f)
    C.hom_eq(compose(C, f, C.cat.id(C.cat.cod(f))), f)
end

function check_assoc(C::DecidableCat, f, g, h)
    C.hom_eq(
        compose(C, compose(C, f, g), h),
        compose(C, f, compose(C, g, h)))
end

# Natural numbers as a one-object category, composition is +, id is 0
nats_cat = Cat(
    f -> :N,        # single object, label it :N
    f -> :N,
    x -> 0,
    (m, n) -> m + n
)

nats = DecidableCat(
    nats_cat,
    (x, y) -> x == y,
    (m, n) -> m == n
)

# Fin — skeleton of finite sets
# objects are Int (cardinalities), morphisms are lookup tables
struct FinMorphism
    dom :: Int
    cod :: Int
    table :: Vector{Int}  # length dom, entries in 0:cod-1
end

function compose_fm(f::FinMorphism, g::FinMorphism)
    @assert f.cod == g.dom "Composites require f.cod == g.dom"
    FinMorphism(f.dom, g.cod, g.table[f.table .+ 1])
end

function eq_fm(f::FinMorphism, g::FinMorphism)
    f.dom == g.dom && f.cod == g.cod && f.table == g.table
end

fin_cat = Cat(
    f -> f.dom,
    f -> f.cod,
    n -> FinMorphism(n, n, collect(0:n-1)),
    (f, g) -> compose_fm(f, g)
)

fin_dcat = DecidableCat(
    fin_cat,
    (m, n) -> m == n,          # object equality: Int == Int
    (f, g) -> eq_fm(f, g)      # morphism equality
)