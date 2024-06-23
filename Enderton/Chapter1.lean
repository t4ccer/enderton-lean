import Mathlib.Data.Nat.Defs

inductive BinOp where
  | And
  | Or
  | Iff
  | Impl

inductive WFF where
  | SentenceSymbol : Nat → WFF
  | Not : (α : WFF) → WFF
  | BinOp : BinOp → (α : WFF) → (β : WFF) → WFF

def WFF.reprAux : WFF → Lean.Format
  | WFF.SentenceSymbol n => "A" ++ reprPrec n 0
  | WFF.Not α => "(¬" ++ α.reprAux ++ ")"
  | WFF.BinOp BinOp.Impl α β => "(" ++ α.reprAux ++ " → " ++ β.reprAux ++ ")"
  | WFF.BinOp BinOp.Iff α β => "(" ++ α.reprAux ++ " ↔ " ++ β.reprAux ++ ")"
  | WFF.BinOp BinOp.Or α β => "(" ++ α.reprAux ++ " ∨ " ++ β.reprAux ++ ")"
  | WFF.BinOp BinOp.And α β => "(" ++ α.reprAux ++ " ∧ " ++ β.reprAux ++ ")"

instance : Repr WFF where
  reprPrec wff _ := wff.reprAux

inductive Symbol where
  | LeftParen
  | RightParen
  | SentenceSymbol : Nat → Symbol
  | BinOp : BinOp → Symbol
  | Not

def WFF.toSymbols : WFF → List Symbol
  | WFF.SentenceSymbol n => [Symbol.SentenceSymbol n]
  | WFF.Not α => [Symbol.LeftParen, Symbol.Not] ++ α.toSymbols ++ [Symbol.RightParen]
  | WFF.BinOp op α β => [Symbol.LeftParen] ++ α.toSymbols ++ [Symbol.BinOp op] ++ β.toSymbols ++ [Symbol.RightParen]

def WFF.length : WFF → Nat
  | SentenceSymbol _ => 1
  | Not α => 3 + α.length
  | BinOp _ α β => 3 + α.length + β.length

def WFF.toSymbols_length_eq_length (w : WFF) : w.toSymbols.length = w.length := by
  induction w with
  | SentenceSymbol _ => rfl
  | Not α ihα =>
    simp [length, toSymbols]
    omega
  | BinOp _ α β ihα ihβ =>
    simp [length, toSymbols]
    omega

theorem WFF.zero_le_length (w : WFF) : 0 < w.length := by
  match w with
  | SentenceSymbol _ =>
    rw [length]
    omega
  | Not _ =>
    rw [length]
    omega
  | BinOp _ _ _ =>
    rw [length]
    omega

theorem WFF.length_not_zero (w : WFF) : w.length ≠ 0 := by
  match w with
  | SentenceSymbol _ => exact Nat.ne_of_beq_eq_false rfl
  | Not _ =>
    rw [length]
    omega
  | BinOp _ _ _ =>
    rw [length]
    omega

theorem WFF.length_one : ∃ (w : WFF), w.length = 1 := by
  exists WFF.SentenceSymbol 0

theorem WFF.length_not_two (w : WFF) : w.length ≠ 2 := by
  match w with
  | SentenceSymbol _ => exact Nat.ne_of_beq_eq_false rfl
  | Not _ =>
    rw [length]
    omega
  | BinOp _ _ _ =>
    rw [length, Nat.add_assoc]
    omega

theorem WFF.length_not_three (w : WFF) : w.length ≠ 3 := by
  match w with
  | SentenceSymbol _ =>
    rw [length]
    exact Nat.ne_of_beq_eq_false rfl
  | Not α =>
    rw [length]
    have h := WFF.zero_le_length α
    omega
  | BinOp _ α _ =>
    rw [length]
    have h := WFF.zero_le_length α
    omega

theorem WFF.length_four : ∃ (w : WFF), w.length = 4 := by
  exists WFF.Not (WFF.SentenceSymbol 0)

theorem WFF.length_five : ∃ (w : WFF), w.length = 5 := by
  exists WFF.BinOp BinOp.And (WFF.SentenceSymbol 0) (WFF.SentenceSymbol 0)

theorem WFF.length_not_six (w : WFF) : w.length ≠ 6 := by
  match w with
  | SentenceSymbol _ =>
    rw [length]
    exact Nat.ne_of_beq_eq_false rfl
  | Not α =>
    rw [length]
    have h := WFF.length_not_three α
    omega
  | BinOp _ α β =>
    rw [length]
    have h1 := WFF.length_not_two α
    have h2 := WFF.length_not_three α
    have h3 := WFF.length_not_two β
    have h4 := WFF.length_not_three β
    omega

-- adapted from Nat.twoStepInduction
def Nat.threeStepInduction
  {P : ℕ → Sort u} (H1 : P 0) (H2 : P 1) (H3 : P 2)
  (H4 : ∀ (n : ℕ) (_IH1 : P n) (_IH2 : P (succ n)) (_IH3 : P (succ (succ n))), P (succ (succ (succ n))))
  : ∀ a : ℕ, P a
  | 0 => H1
  | 1 => H2
  | 2 => H3
  | succ (succ (succ _n)) =>
    H4 _
      (threeStepInduction H1 H2 H3 H4 _)
      (threeStepInduction H1 H2 H3 H4 _)
      (threeStepInduction H1 H2 H3 H4 _)

-- hack to use Nat.threeStepInduction and do not figure out how to impose `le`
-- restriction on `n`, instead let `omega` figure that out in the next proof
theorem WFF.after_six' (n : Nat) : ∃ (w : WFF), w.length = 7 + n := by
  induction n using Nat.threeStepInduction with
  | H1 => exists WFF.Not (WFF.Not (WFF.SentenceSymbol 0))
  | H2 => exists WFF.BinOp BinOp.And (WFF.SentenceSymbol 0) (WFF.Not (WFF.SentenceSymbol 0))
  | H3 => exists WFF.BinOp BinOp.And (WFF.SentenceSymbol 0) (WFF.BinOp BinOp.And (WFF.SentenceSymbol 0) (WFF.SentenceSymbol 0))
  | H4 n h1 h2 h3 =>
    have ⟨w, _⟩ := h1;
    exists WFF.Not w
    rw [length]
    omega

theorem WFF.after_six (n : Nat) (h : 6 < n) : ∃ (w : WFF), w.length = n := by
  let k := n - 7
  have h' : 7 + k = n := by omega
  have w := WFF.after_six' k
  rw [h'] at w
  exact w

theorem WFF.before_six (n : Nat) (h0 : n ≠ 0) (h2 : n ≠ 2) (h3 : n ≠ 3) (h6 : n ≠ 6) (h : n ≤ 6) : ∃ (w : WFF), w.length = n := by
  match n with
  | 0 => omega
  | 1 => exact WFF.length_one
  | 2 => omega
  | 3 => omega
  | 4 => exact WFF.length_four
  | 5 => exact WFF.length_five
  | 6 => omega

theorem WFF.exercise2 (n : Nat) (h0 : n ≠ 0) (h2 : n ≠ 2) (h3 : n ≠ 3) (h6 : n ≠ 6) : ∃ (w : WFF), w.length = n := by
  apply @by_cases (n ≤ 6) _ ?_ ?_
  . intro h
    exact WFF.before_six n h0 h2 h3 h6 h
  . intro h
    refine WFF.after_six n ?h'
    exact Nat.gt_of_not_le h

def WFF.numberOfBinaryConnectives : WFF → Nat
  | WFF.SentenceSymbol _ => 0
  | WFF.Not α => α.numberOfBinaryConnectives
  | WFF.BinOp _ α β => 1 + α.numberOfBinaryConnectives + β.numberOfBinaryConnectives

def WFF.numberOfSentenceSymbols : WFF → Nat
  | WFF.SentenceSymbol _ => 1
  | WFF.Not α => α.numberOfSentenceSymbols
  | WFF.BinOp _ α β => α.numberOfSentenceSymbols + β.numberOfSentenceSymbols

theorem WFF.exercise3 (w : WFF) : w.numberOfSentenceSymbols = w.numberOfBinaryConnectives + 1 := by
  induction w with
  | SentenceSymbol _ =>
    rw [WFF.numberOfBinaryConnectives, WFF.numberOfSentenceSymbols]
  | Not α ihα =>
    rw [WFF.numberOfBinaryConnectives, WFF.numberOfSentenceSymbols]
    exact ihα
  | BinOp _ α β ihα ihβ =>
    rw [WFF.numberOfBinaryConnectives, WFF.numberOfSentenceSymbols]
    omega
