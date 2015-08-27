
(δ (# Combinators:
    (K        λx.λ_.x)                 # (make) a constant function
    (M        λx.x x)                  # self-application
    (Y        (M λu.λf.f (u u f)))     # recursion (Turing)
    # Bool:
    (True     λx.λy.x)
    (False    λx.λy.y)
    # Church numerals:
    (zero     λf.λx.x)
    (zero?    λn.n (K False) True)
    (succ     λn.λf.λx.n f (f x))
    (succ'    λn.λf.λx.f (n f x))
    # List:
    (nil      λonNil.λonCons.onNil)                  # ctor                               c -> _             -> c
    (cons     λx.λxs.λonNil.λonCons.onCons x xs)     # ctor                     a -> b -> _ -> (a -> b -> c) -> c
    (car      λxs.xs ("car" "nil") (λhd.λtl.hd))     # (provoke error on nil)
    (cdr      λxs.xs ("cdr" "nil") (λhd.λtl.tl))     # (provoke error on nil)
    (iterate (Y λself.λf.λx.λonNil.λonCons.onCons x (self f (f x)))   # make a stream
    )
   )
   #(zero? zero)            # λx.λy.x = True
   #(zero? (succ zero))     # λx.λy.y = False
   #(succ (succ (succ zero)))
   
   (iterate succ zero)               # 0...     # diverges if iterate uses cons (?!)
   
   #(car (iterate succ zero))        # λf.λx.x = zero
   #(cdr (iterate succ zero))        # 1...     # diverges if iterate uses cons (?!)
   
   #(car (cdr (iterate succ zero)))  # 1
   #(cdr (cdr (iterate succ zero)))  # 2...     # diverges if iterate uses cons (?!)
   
   #(car (cdr (cdr (iterate succ zero))))
)

