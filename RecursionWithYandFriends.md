### Recursion with Y and Friends

#### One-way (simple) recursion

##### The canonical example, done "by hand"
Well, that of course is the factorial function.
When we try to define like so:
```
  (δ f λn.if (zero? n)
            1
            (* n (f (- n 1))))
```
...we have a problem: what should the `f` mentioned in the body actually be?
If we just say "the same again", well, then the above β-contracts to
```
  (δ f λn.if (zero? n)
            1
            (* n 
               ((λn'.if (zero? n')
                       1
                       (* n' (f (- n' 1))))
                (- n 1))))
```
...and we've just arrived at the *very same problem*, again.
Before even being able to give it a name via δ (remember: δ is no more than that, 
a most simple mechanism for making abbreviations) - we'd had to go through an infinite series of β-contractions (in fact: expansions).

This, in a way, does reflect our intent to write a function that can work on arbitrary
large `n` - but we **don't** want to write down the infinite expansion; 
which, btw, would actually do the job - we simply cannot get hold of it in this manner.

