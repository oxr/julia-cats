struct Cat
    dom :: Function # Mor -> Obj
    cod :: Function # Mor -> Obj
    id :: Function # Obj -> Mor 
    comp :: Function # Mor -> Mor -> Mor
end

struct Func 
    dom :: Cat
    cod :: Cat 
    obj_map :: Function # dom.Obj -> cod.Obj
    mor_map :: Function # dom.Mor -> cod.Mor
end

struct DecideableCat 
    cat :: Cat
    obj_eq :: Function # cat.Obj -> cat.Obj -> Bool
    hom_eq :: Function # a b : cat.Obj -> m n : cat.Mor a b -> Bool
end

# diagramatic order
function compose(C :: DecideableCat, f , g)
    @assert C.obj_eq(C.cod(f), C.dom(g))
    C.comp(f,g)
end

function check_unitl(C :: DecideableCat, f)
    C.hom_eq(
        compose(C, C.id(C.dom(f)), f), 
        f)
end

function check_assoc(C :: DecideableCat, f, g, h)
    C.hom_eq(
        compose(C, compose(C, f , g), h),
        compose(C, f , compose(C,g,h)))
end 


# example : natural numbers, composition is + , id is 0, objects are just 1 , morphisms are numbers
nats_cat = Cat(
        f -> (), #dom
        f -> (), #cod
        x -> 0,  #id
        (m , n) -> m + n #comp
    )


nats = DecideableCat(
        nats_cat,
        (x , y) -> x == y,
        (m , n) -> m == n
    )

    