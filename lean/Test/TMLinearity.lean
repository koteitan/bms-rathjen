/-
Test/TMLinearity.lean — exhaustive linearity check for the order <

Confirms, exhaustively over a finite set of representative terms, that the order
of [R91] 2.3 (as implemented by the decision procedure) is irreflexive, total
(trichotomy) and transitive.  A general proof belongs to Evidence; this is a
sanity check of the implementation.
-/
import TM

namespace TM.Test
open TM.Term

/-- The terms under test (all of them elements of 𝔗(M)). -/
def sample : List Term :=
  let e0 := phi one zero
  let p0 := psi Om zero
  [ zero, one, ofNat 2, omega, plus omega one, add omega omega,
    e0, phi zero e0, phi (ofNat 2) zero, plus e0 omega,
    p0, psi Om one, psi Om p0, plus p0 one,
    Om, Z one, Z omega, Z p0, psi (Z p0) zero,
    M, plus M one, plus M p0, omg (plus M one), omg (plus M omega),
    add (omg (plus M one)) p0 ]

/-- Every element is well-formed. -/
def allWF : Bool := sample.all inT

/-- Trichotomy: distinct terms compare in exactly one direction. -/
def trichotomy : Bool :=
  sample.all fun a => sample.all fun b =>
    if a == b then !(lt a b) && !(lt b a)
    else (lt a b != lt b a)

/-- Irreflexivity. -/
def irrefl : Bool := sample.all fun a => !(lt a a)

/-- Transitivity. -/
def transitive : Bool :=
  sample.all fun a => sample.all fun b => sample.all fun c =>
    !(lt a b) || !(lt b c) || lt a c

#guard allWF
#guard irrefl
#guard trichotomy
#guard transitive

end TM.Test
