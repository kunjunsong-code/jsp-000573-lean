import Init.Data.List.Basic
import Init.Data.List.Lemmas

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

/-!
# JSP-000573 - Lean 4.20.0, no Mathlib

## Question
How large can a set family be if a prescribed pairwise intersection size
is forbidden?

## Answer (for ground set {1,2,3}, forbidden intersection size 1)
Represent subsets of {1,2,3} as bitmasks 0..7. The maximum family of
subsets with no pairwise intersection of size exactly 1 has size 4.
An optimal family: {}, {1}, {2}, {3} (all pairwise intersections have
size 0, which avoids size 1).

All proofs use decide. No sorry, no admit, no native_decide.
-/

def intersectCount (a b : Nat) : Nat :=
  let a0 := a % 2; let a1 := (a / 2) % 2; let a2 := (a / 4) % 2
  let b0 := b % 2; let b1 := (b / 2) % 2; let b2 := (b / 4) % 2
  (if a0 = 1 && b0 = 1 then 1 else 0) +
  (if a1 = 1 && b1 = 1 then 1 else 0) +
  (if a2 = 1 && b2 = 1 then 1 else 0)

def isValidFamily (F : List Nat) : Bool :=
  ! (F.any fun a => F.any fun b => a != b && intersectCount a b = 1)

def all8Families : List (List Nat) :=
  let subs := [0, 1, 2, 3, 4, 5, 6, 7]
  List.range 256 |>.map fun mask =>
    subs |>.filterMap fun (i : Nat) =>
      if (mask / (2^i)) % 2 = 1 then some i else none

def maxFamSize : Nat :=
  all8Families.filter isValidFamily |>.map (·.length) |>.foldl Nat.max 0

theorem maxFamily_3_1 : maxFamSize = 4 := by decide

#print axioms maxFamily_3_1