#eval 1 + 2

#check 1 + 2

#check True -> (False ∨ True)

#eval True -> (False ∨ True)

opaque sunny : Prop
opaque rainy : Prop

#check sunny → ¬ rainy
#check sunny ∧ ¬ sunny

#check Prop                     -- Prop : Type

#check True                     -- True : Prop

#check True.intro               -- True.intro : True

#check sunny /\ rainy

#check sunny ∧ rainy

#check sunny ∨ rainy

def doubleNat : Nat → Nat :=
    fun n : Nat => n * 4

#eval doubleNat 2

-- #eval doubleNat -3

def doubleInt : Int → Int :=
    fun n : Int => n * 2

#eval doubleInt 2

#eval doubleInt (-3)

def threeTimes : (Nat → Nat) → (Nat → Nat) :=
    fun h : Nat → Nat =>
        fun n : Nat => 3 * (h n)

#eval threeTimes doubleNat 2

def add : Nat → Nat → Nat :=
   fun a =>
       fun b => a + b

#check add 2                   -- add 2 : Nat → Nat

#check add 2  3                -- add 2 3 : Nat

#eval add 2 3                  -- 5

def addTwo (a : Nat) (b : Nat) : Nat := a + b

#eval addTwo 2 3              -- 5

def addFour : Nat → Nat → Nat → Nat → Nat :=
    fun a : Nat =>
        fun b : Nat =>
            fun c : Nat =>
                fun d : Nat => a + b + c + d

def addUpFour (n1 n2 n3 n4 : Nat) : Nat := n1 + n2 + n3 + n4

#eval addFour 2 3 4 5        -- 14

#eval addUpFour 4 6 2 9

theorem thmA (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q :=
    And.intro hp hq

#check thmA
#check thmA True
#check thmA True False
#check thmA False False

-- variable (P : Prop)
-- example (h : ¬P) (hp : P) : False :=
--   h hp  -- applying h to hp gives a proof of False

variable (P Q : Prop)

def contingency1 : Prop := P → Q
def contingency2 : Prop := P ∧ ¬ Q

example (hp : P) (hnq : ¬ Q) : contingency2 P Q :=
  ⟨hp, hnq⟩

def bigger : Nat → Prop := fun n : Nat => n > 42

def smaller : Nat → Prop := fun n : Nat => n < 42

#check ∀ n : Nat, bigger n

#check ∃ n : Nat, smaller n

set_option trace.Elab.step true  -- For more detailed tracing
-- set_option trace.Tactic.simp true  -- For tracing simp specifically

example : ¬(smaller 50) := by
  simp [smaller]

example : ¬(smaller 50) := by
  unfold smaller  -- Just unfold the definition without simplifying
  decide

set_option trace.Meta.debug true

example : ¬(smaller 50) := by
  simp [smaller]

example : ¬(smaller 50) := by
  trace "Initial goal: "
  unfold smaller
  trace "After unfolding smaller: "
  simp only [Nat.not_lt]
  trace "After simplifying: "
  decide
-- Basic proof without tracing
example : ¬(smaller 50) := by
  unfold smaller
  apply Nat.not_lt_of_ge
  decide
--   exact Nat.le_refl 50

-- First, just define the theorem without proving it
theorem not_smaller_50 : ¬(smaller 50) := sorry

-- Then check what the type expands to
#print not_smaller_50
-- This should show you the expanded type with smaller unfolded

-- Now try a step-by-step proof
example : ¬(smaller 50) := by
  unfold smaller
  -- Now you should see ¬(50 < 42)
  exact Nat.not_lt_of_ge (by decide)

def biggerThan : Nat → Nat → Prop :=
  fun m =>
    fun n => m > n

#check biggerThan 50 42

#check biggerThan 4 10

def biggerThanBoolean (m n : Nat) : Bool := m > n

#eval biggerThanBoolean 50 42

#eval biggerThanBoolean 4 10

def between : Nat → Nat → Nat → Bool :=
  fun a => fun b => fun c => (a < b) ∧ (b < c)

#check between 1 2 3

#reduce between 1 2 3

#reduce between 6 2 9

#eval between 6 2 9

example : 1 < 2 := by simp

def betweenProp (a b c : Nat) : Prop := (a < b) ∧ (b < c)

example : betweenProp 1 2 3 :=
  have p1 : 1 < 2 := by simp
  have p2 : 2 < 3 := by simp
  show betweenProp 1 2 3 from And.intro p1 p2

inductive dom1 where
    | red : dom1
    | green : dom1
    | blue : dom1

open dom1

#check red

variable (A B C : Prop)

example (a: A) (b: B) : A ∧ B := And.intro a b

example (c : A ∧ B) : A := And.left c

example (c : A ∧ B) : B := And.right c

example : ((False -> False) -> False)  -> False :=
    fun fIMPfIMPf: (False -> False) -> False  =>
        have fIMPf : False -> False := fun f => f
        show False from fIMPfIMPf fIMPf

theorem nonContradiction (A : Prop):  A ∧ (A → False) → False :=
fun proofOfAandNotA : A ∧ (A -> False) =>
have proofOfA : A := And.left proofOfAandNotA
have proofOfAimpliesFalse: A -> False := And.right proofOfAandNotA
show False from proofOfAimpliesFalse proofOfA
-- This declares a theorem named nonContradiction.
-- For any proposition A, if you have a proof of both
--  A and A → False, you can derive False (a contradiction).
-- The proof is given as a function that takes proofOfAandNotA,
--  a proof of A ∧ (A → False).
-- And.left proofOfAandNotA extracts the proof of A from the
--  conjunction.
-- And.right proofOfAandNotA extracts the proof of A → False
--  (i.e., the proof that A leads to a contradiction).
-- Apply proofOfAimpliesFalse (which is a function A → False)
--  to proofOfA (a proof of A).
-- This produces a proof of False, i.e., a contradiction.

example
  (x1 x2 y1 y2 z : Prop)                  -- declare propositions
  (hx1 : x1 → y1 ∨ y2 → z)                -- assumption that x1 is True
  (hx2 : x2 → y1 ∨ y2 → z) :              -- assumption that x2 it True
  ((x1 ∨ x2) ∧ (y1 ∨ y2)) → z :=          -- eligibility rule
    fun h =>
      Or.elim h.left                      -- OR elimination
        (fun hhx1 => hx1 hhx1 h.right)    -- x1 True
        (fun hhx2 => hx2 hhx2 h.right)    -- x2 True

example (x1 x2 y1 y2 z : Prop)                  -- declare propositions
  (hx1 : x1 → y1 ∨ y2 → z) (hx2 : x2 → y1 ∨ y2 → z) :
  ((x1 ∨ x2) ∧ (y1 ∨ y2) → z) :=
    fun h =>
      have hx : x1 ∨ x2 := h.left
      have hy : y1 ∨ y2 := h.right
      show z from
        Or.elim hx
          (fun hhx1 => hx1 hhx1 hy)
          (fun hhx2 => hx2 hhx2 hy)

section
  example
    (x1 x2 y1 y2 z : Prop)                  -- declare propositions
    (hx1 : x1 → y1 ∨ y2 → z)                -- assumption that x1 is True
    (hx2 : x2 → y1 ∨ y2 → z) :              -- assumption that x2 it True
    ((x1 ∨ x2) ∧ (y1 ∨ y2)) → z :=          -- eligibility rule
      fun h =>
        (Or.elim h.left                     -- OR elimination
          (fun hhx1 => hx1 hhx1 h.right)    -- x1 True
          (fun hhx2 => hx2 hhx2 h.right))   -- x2 True
end

section
  example
    (x1 x2 y1 y2 z : Prop)                  -- declare propositions
    (hx1 : x1 → y1 ∨ y2 → z)                -- assumption that x1 is True
    (hx2 : x2 → y1 ∨ y2 → z) :              -- assumption that x2 it True
    ((x1 ∨ x2) ∧ (y1 ∨ y2) → z) :=          -- eligibility rule
      fun h =>
        have hx : x1 ∨ x2 := h.left         -- extract left part of conjunction
        have hy : y1 ∨ y2 := h.right        -- extract right part of conjunction
        show z from                         -- show the proof
          Or.elim hx                        -- OR elimination
            (fun hhx1 => hx1 hhx1 hy)       -- x1 True
            (fun hhx2 => hx2 hhx2 hy)       -- x2 True
end


section

variable (a b c d : Prop)

example : ((b → d) ∧ (¬a → (c ∧ d)) ∧ (a ∨ d) ∧ b ∧ ¬c) → (a ∧ d) := by
  rintro ⟨h1, h2, h3, h4, h5⟩
  -- From b and (b → d), we know d
  have hd : d := h1 h4
  -- From a ∨ d, do cases
  cases h3 with
  | inl ha =>
    -- Case a: just use ha and hd
    exact ⟨ha, hd⟩
  | inr hd' =>
    -- Case d: we must show a ∧ d
    -- Try to prove a by contradiction: if ¬a, then h2 gives c, but ¬c is assumed
    by_cases ha : a
    · exact ⟨ha, hd⟩
    · have hcd := h2 ha
      have hc := hcd.1
      exact absurd hc h5
	  
end



-- theorem ex1 : ∀ x, ¬ provable (conj x False) ∧ (provable x -> ¬ provable False) :=
-- by
--   intro x
--   constructor
--   -- First conjunct: ¬ provable (conj x False)
--   · intro h
--     -- From provable (conj x False), get provable False
--     -- using 'have' tactic for a lemma
--     have hF : provable False := AxConjElimRight x False h
--     -- From provable False, get False
--     exact AxNotPrFalse hF
--   -- Second conjunct: provable x → ¬ provable False
--   · intro hx hF
--     -- From provable False, get False
--     exact AxNotPrFalse hF


-- section
-- variable (a b c d : Prop)

-- example : ((b → d) ∧ (¬a → (c ∧ d)) ∧ (a ∨ d) ∧ b ∧ ¬c) → (a ∧ d) :=
--   fun ⟨h1, h2, h3, h4, h5⟩ =>
--     let hd : d := h1 h4
--     match h3 with
--     | Or.inl ha => ⟨ha, hd⟩
--     | Or.inr hd' =>
--       let ha : a :=
--         fun na : ¬a =>
--           h5 (h2 na).1
--       ⟨ha, hd⟩
-- end