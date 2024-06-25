import Mathlib.Data.Nat.Defs
import Mathlib.Algebra.Parity
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Set.Basic
import Mathlib.Data.Vector
import Mathlib.Data.Vector.Snoc

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

def WFF.eval {n : Nat} (w : WFF n) (v : Fin n → Bool) : Bool :=
  match w with
  | WFF.SentenceSymbol var => v var
  | WFF.Not α => !(WFF.eval α v)
  | WFF.BinOp BinOp.And α β => (WFF.eval α v) && (WFF.eval β v)
  | WFF.BinOp BinOp.Or α β => (WFF.eval α v) || (WFF.eval β v)
  | WFF.BinOp BinOp.Impl α β => !((WFF.eval α v) && !(WFF.eval β v))
  | WFF.BinOp BinOp.Iff α β => (WFF.eval α v) == (WFF.eval β v)

def truthAssignment (n : Nat) : Type := Fin n → Bool

def truthAssignment.satisfies {n : Nat} (v : truthAssignment n) (w : WFF n) : Prop :=
  w.eval v = true

def tautologicallyImplies {n : Nat} (σ : Set (WFF n)) (τ : WFF n) : Prop :=
  ∀ (v : truthAssignment n), v ∈ { v | ∀ (u : WFF n), u ∈ σ → v.satisfies u } → v.satisfies τ

infix:50 " ⊨ " => tautologicallyImplies

def WFF.isTautology {n : Nat} (w : WFF n) : Prop := {} ⊨ w

prefix:75 "⊨" => WFF.isTautology

theorem WFF.self_implies_self {n : Nat} (w : WFF n) : {w} ⊨ w := by
  rw [tautologicallyImplies]
  intros _v hv
  exact hv w rfl

theorem WFF.a_or_not_a_is_tautology :
  ⊨(@WFF.BinOp 1 BinOp.Or (WFF.SentenceSymbol 0) (WFF.Not (WFF.SentenceSymbol 0))) := by
  rw[isTautology, tautologicallyImplies]
  intros v _hv
  rw [truthAssignment.satisfies]
  repeat rw [eval]
  exact Bool.or_not_self (v 0)

def truthAssignment.fromVector {n : Nat} : Vector Bool n → truthAssignment n :=
  fun v i => v.get i

def boolProduct : (n : Nat) → List (Vector Bool n)
  | Nat.zero => [] -- garbage in, garbage out, every (finite) WFF has n > 0 anyway
  | Nat.succ Nat.zero =>
      [(Vector.cons false Vector.nil), (Vector.cons true Vector.nil)]
  | Nat.succ m =>
      (boolProduct m).map (Vector.cons false) ++
      (boolProduct m).map (Vector.cons true)

theorem Vector.length_one_cons (vs : Vector α 1) : vs.tail = Vector.nil := by
  have ⟨ls, hl⟩ := vs
  match ls with
  | List.cons y List.nil => rfl

theorem in_boolProduct {n : Nat} (hn : 0 < n) (xs : Vector Bool n) :
  xs ∈ boolProduct n := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [boolProduct]
    have length_one_cons_bool : ∃ (b : Bool), xs = Vector.cons b Vector.nil := by
      exists xs.head
      rw [<-Vector.cons_head_tail xs, Vector.length_one_cons]
      rfl
    simp
    have ⟨b, hb⟩ := length_one_cons_bool
    rw [hb]
    apply @by_cases (b = true) _ ?_ ?_
    . intro h
      apply Or.inr
      rw [h]
    . intro h
      simp at h
      apply Or.inl
      rw [h]
  | succ n hn ih =>
    rw [boolProduct]
    . simp[*]
      refine exists_or.mp ?succ.a
      rw [<-Vector.cons_head_tail xs]
      exists Vector.tail xs
      apply @by_cases (Vector.head xs = true) _ ?_ ?_
      . intro h
        simp[h]
      . intro h
        simp[h]
    . intro hn0
      rw [hn0] at hn
      absurd hn
      simp

def truthAssignment.prev : truthAssignment (n + 1) → truthAssignment n :=
  fun old var => old var

theorem Vector.get_snoc_last (n : Nat) (xs : Vector α n) (x : α)
  : Vector.get (Vector.snoc xs x) ⟨n, lt_add_one n⟩ = x := by
  induction xs using Vector.inductionOn generalizing x with
  | h_nil => simp
  | h_cons ih => exact ih x

theorem Fin.not_eq (i : Fin (n + 1)) (hi : i.val ≠ n) : i.val < n := by
  omega

theorem Vector.get_cons_nat_succ {n : Nat} (i : Nat) (x : α) (xs : Vector α n) (h : i < n)
  : Vector.get (Vector.cons x xs) ⟨Nat.succ i, Nat.succ_lt_succ h⟩ = Vector.get xs ⟨i, h⟩ := by
  exact rfl

theorem Vector.get_snoc_not_last (n : Nat) (xs : Vector α n) (x : α) (i : Fin (n + 1)) (hi: i.val ≠ n)
  : Vector.get (Vector.snoc xs x) i = Vector.get xs ⟨i.val, Fin.not_eq i hi⟩ := by
  induction xs using Vector.inductionOn generalizing x with
  | h_nil => omega
  | @h_cons m y ys ih =>
    simp
    have ⟨k, hk⟩ := i
    match k with
    | Nat.zero => simp
    | Nat.succ z =>
      simp
      rw [Vector.get_cons_nat_succ, Vector.get_cons_nat_succ]
      . rw [ih]
        . simp at hi
          exact hi
        . omega

theorem truthAssignment.exists_bool_vector {n : Nat} (hn : 0 < n) (v : truthAssignment n) :
  ∃ (bs : Vector Bool n), v = truthAssignment.fromVector bs := by
  induction n, hn using Nat.le_induction with
  | base =>
    exists Vector.cons (v 0) Vector.nil
    apply funext
    intro var
    match var with
    | 0 => simp [truthAssignment.fromVector]
  | succ m _hm ih =>
    have ⟨xs, h_xs⟩ := ih v.prev
    exists Vector.snoc xs (v m)
    simp
    apply funext
    intro var
    rw [truthAssignment.fromVector]
    apply @by_cases (var.val = m) _ ?_ ?_
    . intro h_var
      have is_last := Vector.get_snoc_last m xs (v (Fin.last m))
      have helper : var = ⟨m, by simp⟩ := Fin.val_inj.mp h_var
      rw [helper, is_last]
      rfl
    . intro h_var
      rw [Vector.get_snoc_not_last m xs (v (Fin.last m)) var h_var]
      rw [<-truthAssignment.fromVector, <-h_xs, truthAssignment.prev]
      simp

theorem Or.elim4 {d e : Prop} (h : a ∨ b ∨ c ∨ d) (ha : a → e) (hb : b → e) (hc : c → e) (hd : d → e) : e :=
  Or.elim h ha fun h ↦ Or.elim h hb fun h ↦ Or.elim h hc hd

theorem example_page23 :
  { @WFF.SentenceSymbol 2 0, WFF.BinOp BinOp.Impl (WFF.SentenceSymbol 0) (WFF.SentenceSymbol 1) } ⊨ WFF.SentenceSymbol 1 := by
  rw [tautologicallyImplies]
  intros v hv
  have ⟨bs, h_bs⟩ := truthAssignment.exists_bool_vector (by simp) v
  have bs_in_product := in_boolProduct (by simp) bs
  rw [h_bs] at hv
  rw [h_bs]
  simp [boolProduct, List.map] at bs_in_product
  -- from here we have our function as a disjunction of possible bool assignments
  apply Or.elim4 bs_in_product
  . intro hbv
    simp[truthAssignment.satisfies, truthAssignment.fromVector, WFF.eval, hbv] at hv

  . intro hbv
    simp[truthAssignment.satisfies, truthAssignment.fromVector, WFF.eval, hbv] at hv

  . intro hbv
    simp[truthAssignment.satisfies, truthAssignment.fromVector, WFF.eval, hbv] at hv
    absurd hv -- somehow lean cannot spot contradiction here like in 2 previous cases
    simp
    rfl

  . intro hbv
    simp[truthAssignment.satisfies, truthAssignment.fromVector, WFF.eval, hbv]
    rfl

set_option linter.deprecated false in
theorem WFF.section2_exercise1a : ¬({ @WFF.BinOp 3 BinOp.Iff (WFF.SentenceSymbol 0) (WFF.BinOp BinOp.Iff (WFF.SentenceSymbol 1) (WFF.SentenceSymbol 2)) }
  ⊨ WFF.BinOp BinOp.Or (WFF.BinOp BinOp.And (WFF.SentenceSymbol 0) (WFF.BinOp BinOp.And (WFF.SentenceSymbol 1) (WFF.SentenceSymbol 2))) (WFF.BinOp BinOp.And (WFF.Not (WFF.SentenceSymbol 0)) (WFF.BinOp BinOp.And (WFF.Not (WFF.SentenceSymbol 1)) (WFF.Not (WFF.SentenceSymbol 2))))) := by
  let vb : truthAssignment 3 := truthAssignment.fromVector (Vector.cons false (Vector.cons false (Vector.cons true Vector.nil)))

  intro h
  simp [tautologicallyImplies] at h
  absurd h
  simp
  exists vb
  simp [truthAssignment.satisfies, eval, vb, truthAssignment.fromVector, Vector.get, List.nthLe]
  rfl

set_option linter.deprecated false in
theorem WFF.section2_exercise1b : ¬({ WFF.BinOp BinOp.Or (WFF.BinOp BinOp.And (WFF.SentenceSymbol 0) (WFF.BinOp BinOp.And (WFF.SentenceSymbol 1) (WFF.SentenceSymbol 2))) (WFF.BinOp BinOp.And (WFF.Not (WFF.SentenceSymbol 0)) (WFF.BinOp BinOp.And (WFF.Not (WFF.SentenceSymbol 1)) (WFF.Not (WFF.SentenceSymbol 2)))) }
  ⊨ @WFF.BinOp 3 BinOp.Iff (WFF.SentenceSymbol 0) (WFF.BinOp BinOp.Iff (WFF.SentenceSymbol 1) (WFF.SentenceSymbol 2))) := by
  let vb : truthAssignment 3 := truthAssignment.fromVector (Vector.cons false (Vector.cons false (Vector.cons false Vector.nil)))

  intro h
  simp [tautologicallyImplies] at h
  absurd h
  simp
  exists vb
  simp [truthAssignment.satisfies, eval, vb, truthAssignment.fromVector, Vector.get, List.nthLe]

theorem WFF.isTautology_to_forall {n : Nat} {w : WFF n} (h : ⊨w) : ∀ (v : truthAssignment n), v.satisfies w := by
  simp [isTautology, tautologicallyImplies] at h
  exact h

def WFF.section2_exercise2_σ : Nat → WFF 2
  | Nat.zero => WFF.BinOp BinOp.Impl (WFF.SentenceSymbol 0) (WFF.SentenceSymbol 1)
  | Nat.succ n => WFF.BinOp BinOp.Impl (WFF.section2_exercise2_σ n) (WFF.SentenceSymbol 0)

theorem WFF.section2_exercise2a : ⊨(WFF.section2_exercise2_σ 2) := by
  rw [section2_exercise2_σ, isTautology, tautologicallyImplies]
  intros v hv
  simp [truthAssignment.satisfies, eval, section2_exercise2_σ]

  have ⟨bs, h_bs⟩ := truthAssignment.exists_bool_vector (by simp) v
  have bs_in_product := in_boolProduct (by simp) bs
  rw [h_bs] at hv
  rw [h_bs]
  simp [boolProduct, List.map] at bs_in_product

  apply Or.elim4 bs_in_product
  . intro h
    simp[truthAssignment.satisfies, truthAssignment.fromVector, WFF.eval, h]
  . intro h
    simp[truthAssignment.satisfies, truthAssignment.fromVector, WFF.eval, h]
  . intro h
    simp[truthAssignment.satisfies, truthAssignment.fromVector, WFF.eval, h]
  . intro h
    simp[truthAssignment.satisfies, truthAssignment.fromVector, WFF.eval, h]

theorem WFF.section2_exercise2_σ_0 : ¬(⊨(WFF.section2_exercise2_σ 0)) := by
  rw [section2_exercise2_σ, isTautology, tautologicallyImplies]
  simp [truthAssignment.satisfies, eval, section2_exercise2_σ]
  exists truthAssignment.fromVector (Vector.cons true (Vector.cons false Vector.nil))

theorem WFF.section2_exercise2_σ_1 : ¬(⊨(WFF.section2_exercise2_σ 1)) := by
  rw [section2_exercise2_σ, isTautology, tautologicallyImplies]
  simp [truthAssignment.satisfies, eval, section2_exercise2_σ]
  exists truthAssignment.fromVector (Vector.cons false (Vector.cons false Vector.nil))

theorem Even.succ_succ : Even (Nat.succ (Nat.succ n)) ↔ Even n := by
  apply Iff.intro
  . intro h
    have ⟨m, hm⟩ := h
    exists m - 1
    omega
  . intro h
    have ⟨m, hm⟩ := h
    exists m + 1
    omega

theorem Odd.succ_succ : Odd (Nat.succ (Nat.succ n)) ↔ Odd n := by
  apply Iff.intro
  . intro h
    have ⟨m, hm⟩ := h
    exists m - 1
    omega
  . intro h
    have ⟨m, hm⟩ := h
    exists m + 1
    omega

theorem WFF.section2_exercise2b_evenAux (h_even : Even n) : ⊨(WFF.section2_exercise2_σ (n + 2)) := by
  induction n using Nat.twoStepInduction with
  | H1 =>
    exact WFF.section2_exercise2a
  | H2 =>
    absurd h_even
    exact Nat.not_even_one
  | H3 n ih1 _ih2 =>
    rw [section2_exercise2_σ, section2_exercise2_σ, isTautology, tautologicallyImplies]
    intro v _hv
    simp only [truthAssignment.satisfies]
    rw [eval, eval, eval]
    have prev_h := WFF.isTautology_to_forall (ih1 ?_)
    . rw [prev_h, eval]
      simp
    . exact Even.succ_succ.mp h_even

theorem WFF.section2_exercise2b_even (h_even : Even n) (h_from_two : 1 < n)
  : ⊨(WFF.section2_exercise2_σ n) := by
  let k := n - 2
  have h := @WFF.section2_exercise2b_evenAux k ?k_even
  . have nkh : n = k + 2 := by omega
    rw [nkh]
    exact h
  . have hkn : k + 2 = n := by omega
    rw [<-hkn] at h_even
    exact Even.succ_succ.mp h_even

theorem WFF.section2_exercise2b_oddAux (h_odd : Odd n) : eval (section2_exercise2_σ n) (truthAssignment.fromVector (false ::ᵥ false ::ᵥ Vector.nil)) = false := by
    induction n using Nat.twoStepInduction with
  | H1 =>
    absurd h_odd
    simp
  | H2 =>
    rw [section2_exercise2_σ]
    simp [truthAssignment.satisfies, eval, section2_exercise2_σ, truthAssignment.fromVector]
  | H3 n ih1 _ih2 =>
    simp [section2_exercise2_σ, eval, truthAssignment.fromVector]
    apply ih1
    exact Odd.succ_succ.mp h_odd

theorem WFF.section2_exercise2b_odd (h_odd : Odd n) : ¬(⊨(WFF.section2_exercise2_σ n)) := by
  rw[isTautology, tautologicallyImplies]
  simp
  exists truthAssignment.fromVector (Vector.cons false (Vector.cons false Vector.nil))
  rw [truthAssignment.satisfies]
  rw[WFF.section2_exercise2b_oddAux h_odd]
  simp

theorem WFF.section2_exercise2b : ⊨(WFF.section2_exercise2_σ n) ↔ (Even n ∧ 1 < n) := by
  apply Iff.intro
  . contrapose
    intro h
    rw [not_and_or] at h
    apply Or.elim h
    . intro h_not_even
      have h_odd : Odd n := by exact Nat.odd_iff_not_even.mpr h_not_even
      exact WFF.section2_exercise2b_odd h_odd
    . intro h_lt
      simp at h_lt
      match n with
      | 0 => exact WFF.section2_exercise2_σ_0
      | 1 => exact WFF.section2_exercise2_σ_1
  . intros hs
    have ⟨h_even, h_from_two⟩ := hs
    exact WFF.section2_exercise2b_even h_even h_from_two

theorem WFF.section2_exercise6a {n : Nat} (w : WFF n) (v1 : Fin n → Bool) (v2 : Fin n → Bool) (h : ∀ (x : Fin n), v1 x = v2 x)
  : eval w v1 = eval w v2 := by
  induction w with
  | SentenceSymbol var =>
    rw [eval, eval]
    exact h var
  | Not α ih =>
    rw [eval, eval]
    exact congrArg not ih
  | BinOp op α β ihα ihβ =>
    match op with
    | BinOp.And =>
      rw [eval, eval]
      exact congr (congrArg and ihα) ihβ
    | BinOp.Or =>
      rw [eval, eval]
      exact congr (congrArg or ihα) ihβ
    | BinOp.Impl =>
      rw [eval, eval, Bool.not_and, Bool.not_and]
      exact congr (congrArg or (congrArg not ihα)) (congrArg not (congrArg not ihβ))
    | BinOp.Iff =>
      rw [eval, eval]
      exact congr (congrArg BEq.beq ihα) ihβ
