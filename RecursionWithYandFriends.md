### Recursion with Y and Friends
The famous [fixed-point combinator Y](http://en.wikipedia.org/wiki/Y_combinator).
Lot's of tutorials on it out there...
It is indispensible if we want to implement recursion *generically*, 
ie without any cheating, 
without relying on the host system to provide us with some "magic".
All we need really is already in pure λ.

Btw, in fact there's not only one such Y but infinitely many.
However, we'll content ourselves here with the one discovered by Alan M. Turing
in 1937, and some variations for (multi-way) mutual recursion.

Now, **this tutorial pursues quite an ambitious goal**: 
You will have fully grasped the "why" and "how" of Y, in the sense of a
*persistent* understanding.
Sic! That is, *not* like "yes, I remember to have kind of understood it - once...".
But not only that, even won't need to memorize, or learn by heart, some weird, convoluted, artificial-looking λ-term.
This is because you will always be able to quickly derive it once again for yourself - provided 
of course the tutorial works out for you as intended.

The key thing in achieving this kind of ability is to not only
understand the derivation as such, but rather to understand, to re-enact or actually *feel*
the *motivation* for each and every of the intellectual "moves" taken in the derivation.

Hence it's vital that there's absolutely NO hand-waving or "magic", ever!
This has two sides:
* the author's side (obviously)
* but also that of the reader: she must constantly ask herself whether there's any feeling of unease, of inappropriate "magic", at any point. If that's the case, then the "magic" point must be isolated and marked in mind with a BIG RED TODO - and revisited eventually.

Of course there's a price to pay: 
* the exposition will most probably look overly nitty-gritty and too detailed at first
* it takes endurance, patience and, last but not least, *intellectual discipline and honesty* on the reader's side to get into it. However, if it works out, the period of "getting into it", when it feels like a burden, will be rather short. Thereafter it may very well feel like a game that you just cannot stop playing :)

#### One-way (simple) recursion

##### The canonical example, done "by hand"
Well, that of course is the factorial function.
When we try to define it like so:
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
