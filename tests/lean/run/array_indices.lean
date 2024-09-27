import Lean

/-!
# Tests '.indices` method of `Array`
-/

def sum (arr: Array Nat) : Id Nat := do
  let mut sum := 0
  for ii in arr.indices do
    sum := sum + arr[ii]
  pure sum

def x := #[1, 2, 3, 4, 5]

/-- info: 15 -/
#guard_msgs in
#eval sum x
