
#"foo"  # type str

#42     # ERROR NYI

#λx.x    # type t0 -> t0

#λx.λ_.x   # type t0 -> NQPMu -> t0

#λ_."foo"    # type: NQPMu -> str

#(λx.x) "foo"    # type: t5 where t5 = str

#("foo" "bar")   # Type Error: cannot apply str to str

#("foo" λx.x)   # Type Error: cannot apply str to Void -> t0 where t0 = t5 -> t5

((λx.x) λx.x)   # type: t5 where t5 = Void -> t0; t0 = t6 -> t6

#(δ (# Combinators:
#    #(M λu.u u)                  # self-application
#    #(K λx.λ_.x)                 # (make) a constant function
#    (I λx.x)                    # identity
#   )
#    I "foo"
#)


