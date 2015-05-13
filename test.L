#(λx.λ_.y (x λy.x y z w)) "fo\noö" "bar" "baz" λy.u "qumbl"

#(λx.λ_.(x λy.x y)) "xfo\noö" "xbar" "xbaz" λz."qumbl"

# Turing's Y:
(λU.U U) (λu.λf.f (u u f))

# Turing's Y applied to a function that ignores param self:
#(λU.U U) (λu.λf.f (u u f)) (λself.λx.x)

