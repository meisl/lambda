# ~> Compile Error: unbound variables y, z, w, u
#(λx.λ_.y (x λy.x y z w)) "fo\noö" "bar" "baz" λy.u "qumbl"

# ~> (Runtime) ERROR: cannot apply "xfo\noö" to λy.x y
#(λx.λ_.(x λy.x y)) "xfo\noö" "xbar" "xbaz" λz."qumbl"

#(λy.λz.λx.y (λy.y z)) "y" "z"

# K applied to "foo" and something: ~> "foo"
#(λx.λ_.x) "foo" (λf.λg.λx.f (g x))

# Turing's Y:
#(λU.U U) (λu.λf.f (u u f))

# Turing's Y applied to a function that ignores param self:
#(λU.U U) (λu.λf.f (u u f)) (λself.λx.x)


(δ (# Combinators:
    (I λx.x)                    # identity
    (K λx.λ_.x)                 # (make) a constant function
    (S λf.λg.λx.f x (g x))      # "extended" function composition
    (B λf.λg.λx.f (g x))        # function composition
    (C λf.λx.λy.f y x)          # swap args
    (M λx.x x)                  # self-application
    (Y (M λu.λf.f (u u f)))     # recursion (Turing)
    # Bool:
    (True   λx.λy.x)
    (False  λx.λy.y)
    (and    λp.λq.p q False)
    (or     λp.λq.p True q)
    (not    λp.p False True)
    # List:
    (nil    λonNil.λonCons.onNil)                  # ctor 
    (cons   λx.λxs.λonNil.λonCons.onCons x xs)     # ctor 
    (car    λxs.xs ("car" "nil") (λhd.λtl.hd))     # (provoke error on nil)
    (cdr    λxs.xs ("cdr" "nil") (λhd.λtl.tl))     # (provoke error on nil)
    (foldl  (Y λself.λf.λstart.λxs.
                xs start                            # nil case
                   λhd.λtl.self f (f start hd) tl)) # cons case
    (foldr  (Y λself.λf.λstart.λxs.
                xs start                            # nil case
                   λhd.λtl.f hd (self f start tl))) # cons case
    (map    λf.foldr (λx.λacc.cons (f x) acc) nil)
    (filter λp.foldr (λx.λacc.(p x) (cons x acc) acc) nil)
    (reverse (foldl (C cons) nil))
   )
   #λf.f I K S B C M Y True False and or not nil cons car cdr foldl foldr map filter
   reverse (cons "a" (cons "b" (cons "c" nil)))     # ~> (cons "c" (cons "b" (cons "a" nil)))
   #λ_.K'
)

