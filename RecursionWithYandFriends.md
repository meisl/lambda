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
a most simple mechanism for making abbreviations) - we would have to go through an infinite series of β-contractions (in fact: expansions).

This, in a way, does reflect our intent to write a function that can work on arbitrary
large `n` - but we **don't** want to write down the infinite expansion; 
which, btw, would actually do the job - we simply cannot get hold of it in this manner.

So: we must avoid doing all the expansion work *upfront*, 
and rather somehow defer it until when the function really is applied to some `n`. 
Furthermore, we need to *limit* the expansion that'll be done then to just what's
needed for *that particular* (ie: then known - and finite) `n`.

OK, the problem was that we didn't have a name for it (yet), 
in order to refer to it in the body.
So why not just give it *some*?
The standard - and in fact the only - way to do so in λ is to add a parameter.
Let's call it `self`, and since we'd like to reserve `f` for the "real thing",
the final solution function, we call the intermediate function with the additional
`self` parameter `f'`:
```
  (δ f' λself.λn.if (zero? n)
                   1
                   (* n (self self (- n 1))))
```
This is now all fine and dandy (as far as δ is concerned), 
and we've arrived at it by simply "abstracting away" the problem:
just assume the thing you need but don't have is made somewhere else, somehow,
and *given* to you from the outside.
All that's left to do is to give it a name (`self` here) - and use it.
Even though this might look a bit like cheating at the moment 
it's a perfectly legitimate and actually quite powerful technique, as we'll see.

Now there's one important thing to note about *how `self` is used* in the body of `f'`:
when applied it's not only being fed the decremented `n` as we did in our first attempt.
Rather there's an additional argument coming right before `n`, namely `self` itself!
This is necessary because if - as we pursue - `self` will be `f'` itself, 
then it - as we've just defined - expects exactly these two arguments, not just one `n`.

However, that's not a problem at all; we simply have to give it what it expects.
And that is actually already the final step towards our solution function `f`,
and this step is so incredibly simple that might very well not have seen it alreay:
```
  (δ f (f' f'))
```
Since we're giving it only one argument here - namely itself, as it expects it - this
leaves `f` as a function of one parameter only - namely `n`.
It will expand the "else"-branch only when and as many times as needed.

Note that for this to work, it's crucial to have `if` evaluate only one of its branches at any one time.

If you don't like having the intermediary `f'` "lying about" in global namespace, 
then there's one last refinement:
```
  (δ f (λf'.f' f')
       (λself.λn.if (zero? n)
                   1
                   (* n (self self (- n 1)))))
```

##### "Automating" the pattern (why "fixed-point"?)
The key things we did so far were:
* introduce additional parameter `self`
* use it in intermediary function `f'` - but never forget to give it itself as first, additional argument
* apply `f'` to itself; this yields the solution function

The second point is interesting.
Let's just meditate a bit on the following intermediate function `f''`, 
which is slightly (but crucially!) different from `f'`:
```
  (δ f'' λself.λn.if (zero? n)
                    1
                    (* n (self (- n 1))))
```
Can you spot the difference to `f'`?

We've left out the additional argument `self` in the application of `self`.
But - haven't we just emphasized NOT to do this?
Well, on the one hand this indeed looks plainly wrong, 
since applying *that* to itself will definitely *not* yield the intended solution function.
