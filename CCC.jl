include("Cats.jl");          using .Cats
include("Functors.jl");      using .Functors
include("Fin.jl");           using .Fin
include("Constructions.jl"); using .Constructions

Δ(C) = Func(
            C, 
            prod_cat(C,C), 
            x -> (x,x), 
            f -> (f,f)
        )


∏(C) = Func(
            prod_cat(C,C), 
            C, 
            (x,y) -> prod_obj(C, x,y), 
            (f,g) -> prod_mor(C, f,g)
        )

∐(C) = Func(
            coprod_cat(C,C), 
            C, 
            (x,y) -> coprod_obj(C, x,y), 
            (f,g) -> coprod_mor(C, f,g)
        )

prod_adjoint(C) = Adjunction(Δ(C), ∏(C),prod_epsilon, prod_eta)


prod_epsilon = NatTrans(
    ∏(C), 
    Func(C,C), 
    (x,y) -> prod_proj(C, x,y), 
    (f,g) -> prod_proj_mor(C, f,g)
)