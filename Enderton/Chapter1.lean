import Mathlib.Data.Nat.Defs
import Mathlib.Algebra.Parity

inductive BinOp where
  | And
  | Or
  | Iff
  | Impl

inductive WFF (n : Nat) where
  | SentenceSymbol : Fin n → WFF n
  | Not : (α : WFF n) → WFF n
  | BinOp : BinOp → (α : WFF n) → (β : WFF n) → WFF n

def WFF.reprAux {n : Nat} : WFF n → Lean.Format
  | WFF.SentenceSymbol n => "A" ++ reprPrec n 0
  | WFF.Not α => "(¬" ++ α.reprAux ++ ")"
  | WFF.BinOp BinOp.Impl α β => "(" ++ α.reprAux ++ " → " ++ β.reprAux ++ ")"
  | WFF.BinOp BinOp.Iff α β => "(" ++ α.reprAux ++ " ↔ " ++ β.reprAux ++ ")"
  | WFF.BinOp BinOp.Or α β => "(" ++ α.reprAux ++ " ∨ " ++ β.reprAux ++ ")"
  | WFF.BinOp BinOp.And α β => "(" ++ α.reprAux ++ " ∧ " ++ β.reprAux ++ ")"

instance : Repr (WFF n) where
  reprPrec wff _ := wff.reprAux

inductive Symbol where
  | LeftParen
  | RightParen
  | SentenceSymbol : Nat → Symbol
  | BinOp : BinOp → Symbol
  | Not

def WFF.toSymbols {n : Nat} : WFF n → List Symbol
  | WFF.SentenceSymbol n => [Symbol.SentenceSymbol n]
  | WFF.Not α => [Symbol.LeftParen, Symbol.Not] ++ α.toSymbols ++ [Symbol.RightParen]
  | WFF.BinOp op α β => [Symbol.LeftParen] ++ α.toSymbols ++ [Symbol.BinOp op] ++ β.toSymbols ++ [Symbol.RightParen]

def WFF.length {n : Nat} : WFF n → Nat
  | SentenceSymbol _ => 1
  | Not α => 3 + α.length
  | BinOp _ α β => 3 + α.length + β.length

def WFF.toSymbols_length_eq_length {n : Nat} (w : WFF n) : w.toSymbols.length = w.length := by
  induction w with
  | SentenceSymbol _ => rfl
  | Not α ihα =>
    simp [length, toSymbols]
    omega
  | BinOp _ α β ihα ihβ =>
    simp [length, toSymbols]
    omega

theorem WFF.zero_le_length {n : Nat} (w : WFF n) : 0 < w.length := by
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

theorem WFF.length_not_zero {n : Nat} (w : WFF n) : w.length ≠ 0 := by
  match w with
  | SentenceSymbol _ => exact Nat.ne_of_beq_eq_false rfl
  | Not _ =>
    rw [length]
    omega
  | BinOp _ _ _ =>
    rw [length]
    omega

theorem WFF.length_one {n : Nat} (hn : 0 < n) : ∃ (w : WFF n), w.length = 1 := by
  exists WFF.SentenceSymbol ⟨0, hn⟩

theorem WFF.length_not_two {n : Nat} (w : WFF n) : w.length ≠ 2 := by
  match w with
  | SentenceSymbol _ => exact Nat.ne_of_beq_eq_false rfl
  | Not _ =>
    rw [length]
    omega
  | BinOp _ _ _ =>
    rw [length, Nat.add_assoc]
    omega

theorem WFF.length_not_three {n : Nat} (w : WFF n) : w.length ≠ 3 := by
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

theorem WFF.length_four {n : Nat} (hn : 0 < n) : ∃ (w : WFF n), w.length = 4 := by
  exists WFF.Not (WFF.SentenceSymbol ⟨0, hn⟩)

theorem WFF.length_five {n : Nat} (hn : 0 < n) : ∃ (w : WFF n), w.length = 5 := by
  exists WFF.BinOp BinOp.And (WFF.SentenceSymbol ⟨0, hn⟩) (WFF.SentenceSymbol ⟨0, hn⟩)

theorem WFF.length_not_six {n : Nat} (w : WFF n) : w.length ≠ 6 := by
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
theorem WFF.after_six' {n : Nat} (hn : 0 < n) (k : Nat) : ∃ (w : WFF n), w.length = 7 + k := by
  induction k using Nat.threeStepInduction with
  | H1 => exists WFF.Not (WFF.Not (WFF.SentenceSymbol ⟨0, hn⟩))
  | H2 => exists WFF.BinOp BinOp.And (WFF.SentenceSymbol ⟨0, hn⟩) (WFF.Not (WFF.SentenceSymbol ⟨0, hn⟩))
  | H3 => exists WFF.BinOp BinOp.And (WFF.SentenceSymbol ⟨0, hn⟩) (WFF.BinOp BinOp.And (WFF.SentenceSymbol ⟨0, hn⟩) (WFF.SentenceSymbol ⟨0, hn⟩))
  | H4 n h1 h2 h3 =>
    have ⟨w, _⟩ := h1;
    exists WFF.Not w
    rw [length]
    omega

theorem WFF.after_six {n : Nat} (hn : 0 < n) (k : Nat) (h : 6 < k) : ∃ (w : WFF n), w.length = k := by
  let m := k - 7
  have h' : 7 + m = k := by omega
  have w := @WFF.after_six' n hn m
  rw [h'] at w
  exact w

theorem WFF.before_six {n : Nat} (hn : 0 < n) (k : Nat) (h0 : k ≠ 0) (h2 : k ≠ 2) (h3 : k ≠ 3) (h6 : k ≠ 6) (h : k ≤ 6)
  : ∃ (w : WFF n), w.length = k := by
  match k with
  | 0 => omega
  | 1 => exact WFF.length_one hn
  | 2 => omega
  | 3 => omega
  | 4 => exact WFF.length_four hn
  | 5 => exact WFF.length_five hn
  | 6 => omega

theorem WFF.section1_exercise2 {n : Nat} (hn : 0 < n) (k : Nat) (h0 : k ≠ 0) (h2 : k ≠ 2) (h3 : k ≠ 3) (h6 : k ≠ 6)
  : ∃ (w : WFF n), w.length = k := by
  apply @by_cases (k ≤ 6) _ ?_ ?_
  . intro h
    exact WFF.before_six hn k h0 h2 h3 h6 h
  . intro h
    refine WFF.after_six hn k ?h'
    exact Nat.gt_of_not_le h

def WFF.numberOfBinaryConnectives {n : Nat} : WFF n → Nat
  | WFF.SentenceSymbol _ => 0
  | WFF.Not α => α.numberOfBinaryConnectives
  | WFF.BinOp _ α β => 1 + α.numberOfBinaryConnectives + β.numberOfBinaryConnectives

def WFF.numberOfSentenceSymbols {n : Nat} : WFF n → Nat
  | WFF.SentenceSymbol _ => 1
  | WFF.Not α => α.numberOfSentenceSymbols
  | WFF.BinOp _ α β => α.numberOfSentenceSymbols + β.numberOfSentenceSymbols

theorem WFF.section1_exercise3 {n : Nat} (w : WFF n)
  : w.numberOfSentenceSymbols = w.numberOfBinaryConnectives + 1 := by
  induction w with
  | SentenceSymbol _ =>
    rw [WFF.numberOfBinaryConnectives, WFF.numberOfSentenceSymbols]
  | Not α ihα =>
    rw [WFF.numberOfBinaryConnectives, WFF.numberOfSentenceSymbols]
    exact ihα
  | BinOp _ α β ihα ihβ =>
    rw [WFF.numberOfBinaryConnectives, WFF.numberOfSentenceSymbols]
    omega

def WFF.hasNoNegationB {n : Nat} : WFF n → Bool
  | WFF.SentenceSymbol _ => true
  | WFF.Not _ => false
  | WFF.BinOp _ α β => α.hasNoNegationB && β.hasNoNegationB

def WFF.hasNoNegation {n : Nat} (w : WFF n) : Prop := w.hasNoNegationB = true

def and_left : ((a && b) = true) → (a = true) := by
  intro h
  rw [and] at h
  refine @by_cases (a = true) _ ?_ ?_
  . exact fun a ↦ a
  . intro h'
    simp at h'
    rw [h'] at h
    simp at h

def and_right : ((a && b) = true) → (b = true) := by
  intro h
  rw [Bool.and_comm] at h
  exact and_left h

def WFF.BinOp_hasNoNegation {n : Nat} {α β : WFF n} (h : (WFF.BinOp op α β).hasNoNegation)
  : α.hasNoNegation ∧ β.hasNoNegation := by
  rw [hasNoNegation, hasNoNegationB] at h
  have hα := and_left h
  have hβ := and_right h
  exact { left := hα, right := hβ }

def WFF.Not_hasNoNegation {n : Nat} {α : WFF n} (h : (WFF.Not α).hasNoNegation) : False := by
  rw [hasNoNegation, hasNoNegationB] at h
  absurd h
  simp

theorem WFF.length_if_hasNoNegation {n : Nat} (w : WFF n) (h : w.hasNoNegation) : ∃ k, w.length = 4 * k + 1 := by
  induction w with
  | SentenceSymbol _ =>
    rw [length]
    exists 0
  | Not _ _ =>
    exact (WFF.Not_hasNoNegation h).elim
  | BinOp _ α β ihα ihβ =>
    rw [length]
    have ⟨hα, hβ⟩ := WFF.BinOp_hasNoNegation h
    have hoα := ihα hα
    have hoβ := ihβ hβ
    have ⟨kα, hkα⟩ := hoα
    have ⟨kβ, hkβ⟩ := hoβ
    rw [Nat.add_assoc, Nat.add_comm, hkα, hkβ]
    exists kα + kβ + 1
    omega

theorem WFF.section1_exercise5a {n : Nat} (w : WFF n) (h : w.hasNoNegation)
  : Odd (w.length) := by
  have ⟨l, hl⟩ := WFF.length_if_hasNoNegation w h
  rw [hl]
  exists 2 * l
  omega

theorem WFF.section1_exercise5b {n : Nat} {k : Nat} (w : WFF n) (h_neg : w.hasNoNegation) (h_len : w.length = 4 * k + 1)
  : w.numberOfSentenceSymbols = k + 1 := by
  induction w generalizing k with
  | SentenceSymbol _ =>
    rw [numberOfSentenceSymbols]
    rw [length] at h_len
    have k0 : k = 0 := by omega
    rw [k0]
  | Not _ _ =>
    exact (WFF.Not_hasNoNegation h_neg).elim
  | BinOp _ α β ihα ihβ =>
    have ⟨hα, hβ⟩ := WFF.BinOp_hasNoNegation h_neg
    have ⟨kα, hkα⟩ := WFF.length_if_hasNoNegation α hα
    have ⟨kβ, hkβ⟩ := WFF.length_if_hasNoNegation β hβ
    rw [length, hkα, hkβ] at h_len
    rw [hkα] at ihα
    rw [hkβ] at ihβ
    have noss_α : numberOfSentenceSymbols α = kα + 1 := ihα hα rfl
    have noss_β : numberOfSentenceSymbols β = kβ + 1 := ihβ hβ rfl
    rw [numberOfSentenceSymbols, noss_α, noss_β]
    omega
