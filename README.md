# Jeans

We have a fairly well-known piece of kit that uses a theorem prover to find all
total Haskell functions with a given type. (`djinn`.)

We have a way to use Template Haskell to reflect those into real Haskell functions. (`djinn-th`.)

We have property testing to help verify equational laws. (`QuickCheck` etc.)

This brings up two possibilities:

* Write your own types and have law-abiding Functor/Applicative/Monad/Monoid/Foldable etc. instances
  generated automatically if they exist.
* My original goal: generate random ADTs, including ones with function types in them, and see
  if they admit interesting instances of Applicative, Monad, or other "control" structures that aren't obvious
  combinations of well-known ones. (E.g. `StateT (Reader r) a` isn't interesting.) In essence,
  I'd like my laptop to search for new monads, at the price of a bit of CPU load. :)

Well, eventually.

# License

BSD3.

## Original file header

```
Modified to use Template Haskell by Claude Heiland-Allen, August 2010

Copyright (c) 2005, 2008 Lennart Augustsson
See LICENSE for licensing details.

Intuitionistic theorem prover
Written by Roy Dyckhoff, Summer 1991
Modified to use the LWB syntax  Summer 1997
and simplified in various ways...

Translated to Haskell by Lennart Augustsson December 2005

Incorporates the Vorob'ev-Hudelmaier etc calculus (I call it LJT)
See RD's paper in JSL 1992:
"Contraction-free calculi for intuitionistic logic"

Torkel Franzen (at SICS) gave me good ideas about how to write this
properly, taking account of first-argument indexing,
and I learnt a trick or two from Neil Tennant's "Autologic" book.
```
