{-# OPTIONS --without-K #-}

module inconsistency-continuity where
import Level as L
open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Data.Bool
open import Data.Product
open import Data.Sum
open import Data.Nat
open import Data.Vec
open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary.Decidable
open ≡-Reasoning

𝟘 𝟙 𝟚 : Set
𝟘 = ⊥
𝟙 = ⊤
𝟚 = Bool

J : ∀ {ℓ ℓ'} {A : Set ℓ} (C : (x y : A) (p : x ≡ y) → Set ℓ')
  → ((x : A) → C x x refl)
  → ((x y : A) (p : x ≡ y) → C x y p)
J C c x .x refl = c x

discrete : Set → Set
discrete A = ∀(a a' : A) → Dec (a ≡ a')

constant : ∀ {ℓ₁ ℓ₂} {X : Set ℓ₁} {Y : Set ℓ₂} → (X → Y) → Set(ℓ₁ L.⊔ ℓ₂)
constant f = ∀ x x' → f x ≡ f x'

suc-injective : ∀{i j : ℕ} → suc i ≡ suc j → i ≡ j
suc-injective = cong pred

ℕ-discrete : discrete ℕ
ℕ-discrete zero zero = yes refl
ℕ-discrete zero (suc m) = no (λ ())
ℕ-discrete (suc n) zero = no (λ ())
ℕ-discrete (suc n) (suc m) = lemma (ℕ-discrete n m)
  where
  lemma : Dec (n ≡ m) → Dec (suc n ≡ suc m)
  lemma (yes p) = yes (cong suc p)
  lemma (no ¬p) = no (λ x → ¬p (suc-injective x))

𝟚-discrete : discrete 𝟚
𝟚-discrete false false = yes refl
𝟚-discrete false true = no (λ ())
𝟚-discrete true false = no (λ ())
𝟚-discrete true true = yes refl

𝟚≡T∨F : (b : 𝟚) → (b ≡ true) ⊎ (b ≡ false)
𝟚≡T∨F false = inj₂ refl
𝟚≡T∨F true = inj₁ refl

Lemma[b≡true∨b≡false] : {b : 𝟚} → (b ≡ true) ⊎ (b ≡ false)
Lemma[b≡true∨b≡false] {false} = inj₂ refl
Lemma[b≡true∨b≡false] {true} = inj₁ refl

Lemma[b≠true→b≡false] : {b : 𝟚} → ¬ (b ≡ true) → b ≡ false
Lemma[b≠true→b≡false] {false} ¬p = refl
Lemma[b≠true→b≡false] {true} ¬p = ⊥-elim (¬p refl)

Lemma[b≠false→b≡true] : {b : 𝟚} → ¬ (b ≡ false) → b ≡ true
Lemma[b≠false→b≡true] {false} ¬p = ⊥-elim (¬p refl)
Lemma[b≠false→b≡true] {true} ¬p = refl

≤-refl : {n : ℕ} → n ≤ n
≤-refl {0}      = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : {i j k : ℕ} → i ≤ j → j ≤ k → i ≤ k
≤-trans z≤n _ = z≤n
≤-trans (s≤s a) (s≤s b) = s≤s (≤-trans a b)

≤-suc : {n m : ℕ} → n ≤ m → n ≤ suc m
≤-suc z≤n = z≤n
≤-suc (s≤s a) = s≤s (≤-suc a)

n≤m+1→n≤m∨n≡m+1 : {n m : ℕ} → n ≤ suc m → (n ≤ m) ⊎ (n ≡ suc m)
n≤m+1→n≤m∨n≡m+1 {zero} {zero} n≤m+1 = inj₁ z≤n
n≤m+1→n≤m∨n≡m+1 {zero} {suc m} n≤m+1 = inj₁ z≤n
n≤m+1→n≤m∨n≡m+1 {suc .0} {zero} (s≤s z≤n) = inj₂ refl
n≤m+1→n≤m∨n≡m+1 {suc n} {suc m} (s≤s n≤m+1) with n≤m+1→n≤m∨n≡m+1 {m = m} n≤m+1
n≤m+1→n≤m∨n≡m+1 {suc n} {suc m} (s≤s n≤m+1) | inj₁ n≤m = inj₁ (s≤s n≤m)
n≤m+1→n≤m∨n≡m+1 {suc n} {suc m} (s≤s n≤m+1) | inj₂ n≡m+1 = inj₂ (cong suc n≡m+1)

m≤n∧n≤m→m=n : {n m : ℕ} → m ≤ n → n ≤ m → m ≡ n
m≤n∧n≤m→m=n {zero} {zero} z≤n z≤n = refl
m≤n∧n≤m→m=n {zero} {suc m} () n≤m
m≤n∧n≤m→m=n {suc n} {zero} z≤n ()
m≤n∧n≤m→m=n {suc n} {suc m} (s≤s m≤n) (s≤s n≤m) = sym (cong suc (m≤n∧n≤m→m=n n≤m m≤n))

n≰m→m<n : {n m : ℕ} → ¬ (n ≤ m) → m < n
n≰m→m<n {zero} {m} n≰m = ⊥-elim (n≰m z≤n)
n≰m→m<n {suc n} {zero} n≰m = s≤s z≤n
n≰m→m<n {suc n} {suc m} n≰m = s≤s (n≰m→m<n (λ z → n≰m (s≤s z)))

sucn≡n+1 : {n : ℕ} → suc n ≡ n + 1
sucn≡n+1 {zero} = refl
sucn≡n+1 {suc n} = cong suc sucn≡n+1

indℕ : ∀ {ℓ} {C : ℕ → Set ℓ} → C zero → ((n : ℕ) → C n → C (suc n)) → (n : ℕ) → C n
indℕ c₀ cs zero = c₀
indℕ c₀ cs (suc n) = cs n (indℕ c₀ cs n)

sindℕ : ∀ {ℓ} {C : ℕ → Set ℓ} → (∀ n → (∀ m → m < n → C m) → C n) → ∀ n → C n
sindℕ {ℓ} {C} IH n = IH n (indℕ {C = λ n → (m : ℕ) → suc m ≤ n → C m}
                                (λ m ())
                                (λ { n Cₙ m (s≤s m≤n) → IH m (λ k k<m → Cₙ k (≤-trans k<m m≤n))}) n)

------------------------------------------------------------------------


Baire : Set
Baire = ℕ → ℕ

Cantor : Set
Cantor = ℕ → 𝟚


------------------------------------------------------------------------

_⟪_⟫ : {X : Set} → (ℕ → X) → (n : ℕ) → Vec X n
α ⟪ zero ⟫ = []
α ⟪ suc n ⟫ = α 0 ∷ ((λ n → α (suc n)) ⟪ n ⟫)

_≡⟪_⟫_ : {X : Set} → (ℕ → X) → ℕ → (ℕ → X) → Set
α ≡⟪ n ⟫ β = (α ⟪ n ⟫) ≡ (β ⟪ n ⟫)

_C∷_ : {n : ℕ} → Vec 𝟚 n → Cantor → Cantor
_C∷_ [] α = α
_C∷_ (x ∷ s) α zero = x
_C∷_ (x ∷ s) α (suc n) = (s C∷ α) n

[0^_][_*] : ℕ → ℕ → Baire
[0^ zero ][ i *] m = i 
[0^ suc n ][ i *] zero = 0
[0^ suc n ][ i *] (suc m) = [0^ n ][ i *] m

0* : Baire
0* _ = 0

0₂* 1₂* : Cantor
0₂* _ = false
1₂* _ = true

[0^_][_*]≡k : (n k : ℕ) → ([0^ n ][ k *] n) ≡ k
[0^ zero ][ k *]≡k = refl
[0^ suc n ][ k *]≡k = [0^ n ][ k *]≡k

[0^_][_*]0≡0 : (n k : ℕ) → ([0^ n + 1 ][ k *] 0) ≡ 0
[0^ zero ][ k *]0≡0 = refl
[0^ suc n ][ k *]0≡0 = refl

0*≡⟪⟫[0^_][_*] : (n k : ℕ) → 0* ≡⟪ n ⟫ [0^ n ][ k *]
0*≡⟪⟫[0^ n ][ k *] = trans 0*≡⟪n⟫0ⁿ 0ⁿ≡⟪n⟫[0^n][k*]
  where
  0ⁿ : {n : ℕ} → Vec ℕ n
  0ⁿ {zero} = []
  0ⁿ {suc n} = 0 ∷ 0ⁿ

  0*≡⟪n⟫0ⁿ : {n : ℕ} → 0* ⟪ n ⟫ ≡ 0ⁿ
  0*≡⟪n⟫0ⁿ {zero} = refl
  0*≡⟪n⟫0ⁿ {suc n} = cong (λ xs → 0 ∷ xs) 0*≡⟪n⟫0ⁿ

  0ⁿ≡⟪n⟫[0^n][k*] : {n : ℕ} → 0ⁿ ≡ ([0^ n ][ k *] ⟪ n ⟫)
  0ⁿ≡⟪n⟫[0^n][k*] {zero} = refl
  0ⁿ≡⟪n⟫[0^n][k*] {suc n} = cong (λ xs → 0 ∷ xs) 0ⁿ≡⟪n⟫[0^n][k*]

0*≡⟪⟫[0^_+1][_*] : (n k : ℕ) → 0* ≡⟪ n ⟫ [0^ n + 1 ][ k *]
0*≡⟪⟫[0^ n +1][ k *] = trans 0*≡⟪n⟫0ⁿ 0ⁿ≡⟪n⟫[0^n+1][k*]
  where
  0ⁿ : {n : ℕ} → Vec ℕ n
  0ⁿ {zero} = []
  0ⁿ {suc n} = 0 ∷ 0ⁿ

  0*≡⟪n⟫0ⁿ : {n : ℕ} → 0* ⟪ n ⟫ ≡ 0ⁿ
  0*≡⟪n⟫0ⁿ {zero} = refl
  0*≡⟪n⟫0ⁿ {suc n} = cong (λ xs → 0 ∷ xs) 0*≡⟪n⟫0ⁿ

  0ⁿ≡⟪n⟫[0^n+1][k*] : {n : ℕ} → 0ⁿ ≡ ([0^ n + 1 ][ k *] ⟪ n ⟫)
  0ⁿ≡⟪n⟫[0^n+1][k*] {zero} = refl
  0ⁿ≡⟪n⟫[0^n+1][k*] {suc n} = cong (λ xs → 0 ∷ xs) 0ⁿ≡⟪n⟫[0^n+1][k*]

cons≡ : {X : Set} {n : ℕ} {x y : X} {xs ys : Vec X n}
      → x ≡ y → xs ≡ ys → x ∷ xs ≡ y ∷ ys
cons≡ {X} {n} {x} {.x} {xs} {.xs} refl refl = refl

append≡ : {X : Set} {n : ℕ} (α : Cantor) → α ⟪ n + 1 ⟫ ≡ (α ⟪ n ⟫ ++ [ α n ])
append≡ {X} {zero} α = refl
append≡ {X} {suc n} α = cong (_∷_ (α zero)) (append≡ {X} {n} (λ z → α (suc z)))

⟪_+1⟫_ : {X : Set} {n : ℕ} {α β : Cantor} → α ≡⟪ n ⟫ β
     → α n ≡ β n → α ≡⟪ n + 1 ⟫ β
⟪_+1⟫_ {X} {n} {α} {β} p q =
       (α ⟪ n + 1 ⟫)
    ≡⟨ append≡ {X} {n} α ⟩
       α ⟪ n ⟫ ++ [ α n ]
    ≡⟨ cong (λ αₙ → (α ⟪ n ⟫) ++ [ αₙ ]) q ⟩
       α ⟪ n ⟫ ++ [ β n ]
    ≡⟨ cong (λ βs → βs ++ [ β n ]) p ⟩
       β ⟪ n ⟫ ++ [ β n ]
    ≡⟨ sym (append≡ {X} {n} β) ⟩
       β ⟪ n + 1 ⟫ ∎

⟪_-1⟫ : {X : Set} {α β : ℕ → X} {n : ℕ}
      → α ≡⟪ n + 1 ⟫ β
      → α ≡⟪ n ⟫ β
⟪_-1⟫ {X} {α} {β} {zero} eq = refl
⟪_-1⟫ {X} {α} {β} {suc n} eq = cons≡ (cong head eq) ⟪ cong tail eq -1⟫

s∷≡⟪n⟫ : {n : ℕ} → (s : Vec 𝟚 n) → (α β : Cantor) → (s C∷ α) ≡⟪ n ⟫ (s C∷ β)
s∷≡⟪n⟫ [] α β = refl
s∷≡⟪n⟫ (x ∷ s) α β = cong (λ xs → x ∷ xs) (s∷≡⟪n⟫ s α β)

s∷≡⟪m≤n⟫ : {n m : ℕ} → (s : Vec 𝟚 n) → (α β : Cantor) → m ≤ n → (s C∷ α) ≡⟪ m ⟫ (s C∷ β)
s∷≡⟪m≤n⟫ [] α β z≤n = refl
s∷≡⟪m≤n⟫ (x ∷ s) α β z≤n = refl
s∷≡⟪m≤n⟫ (x ∷ s) α β (s≤s m≤n) = cong (_∷_ x) (s∷≡⟪m≤n⟫ s α β m≤n)

α≡⟪n⟫α[n]∷β : {n : ℕ} {α β : Cantor} → α ≡⟪ n ⟫ ((α ⟪ n ⟫) C∷ β)
α≡⟪n⟫α[n]∷β {zero} {α} {β} = refl
α≡⟪n⟫α[n]∷β {suc n} {α} {β} = cong (_∷_ (α zero)) α≡⟪n⟫α[n]∷β

α⟪n⟫∷β[n]≡β0 : {n : ℕ} {α β : Cantor} → ((α ⟪ n ⟫) C∷ β) n ≡ β 0
α⟪n⟫∷β[n]≡β0 {zero} = refl
α⟪n⟫∷β[n]≡β0 {suc n} = α⟪n⟫∷β[n]≡β0 {n}

Dec[Vec𝟚] : {n : ℕ} → (P : Vec 𝟚 n → Set)
          → (∀ s → Dec (P s)) → Dec (∀ s → P s)
Dec[Vec𝟚] {zero} P Dec[Ps] with (Dec[Ps] [])
Dec[Vec𝟚] {zero} P Dec[Ps] | yes p = yes (λ { [] → p })
Dec[Vec𝟚] {zero} P Dec[Ps] | no ¬p = no (λ p → ¬p (p []))
Dec[Vec𝟚] {suc n} P Dec[Ps] with Dec[Vec𝟚] (λ s → P (true ∷ s))
                                           (λ s → Dec[Ps] (true ∷ s))
Dec[Vec𝟚] {suc n} P Dec[Ps] | yes p with Dec[Vec𝟚] (λ s → P (false ∷ s))
                                                   (λ s → Dec[Ps] (false ∷ s))
Dec[Vec𝟚] {suc n} P Dec[Ps] | yes p₀ | yes p₁ = yes (λ { (false ∷ s) → p₁ s
                                                       ; (true ∷ s) → p₀ s })
Dec[Vec𝟚] {suc n} P Dec[Ps] | yes p | no ¬p = no (λ p → ¬p (λ s → p (false ∷ s)))
Dec[Vec𝟚] {suc n} P Dec[Ps] | no ¬p = no (λ p → ¬p (λ s → p (true ∷ s)))

min-Dec[_] : (A : ℕ → Set) → (n : ℕ) → (∀ m → m ≤ n → Dec (A m))
           → (∀ m → m ≤ n → ¬(A m)) ⊎ (Σ[ m ∈ ℕ ] m ≤ n × A m)
min-Dec[ A ] zero Dec[m≤n] with Dec[m≤n] 0 z≤n
min-Dec[ A ] zero Dec[m≤n] | yes A₀ = inj₂ (zero , z≤n , A₀)
min-Dec[ A ] zero Dec[m≤n] | no ¬A₀ = inj₁ (λ { zero z≤n Aₘ → ¬A₀ Aₘ
                                             ; (suc m) () Aₘ})
min-Dec[ A ] (suc n) Dec[m≤n] with Dec[m≤n] (suc n) ≤-refl
min-Dec[ A ] (suc n) Dec[m≤n] | yes Aₙ₊₁ = inj₂ (suc n , ≤-refl , Aₙ₊₁)
min-Dec[ A ] (suc n) Dec[m≤n] | no ¬Aₙ₊₁
             with min-Dec[ A ] n (λ m m≤n → Dec[m≤n] m (≤-suc m≤n))
min-Dec[ A ] (suc n) Dec[m≤n] | no ¬Aₙ₊₁ | (inj₁ ¬minₙ) = inj₁ ¬minₙ₊₁
  where
  ¬minₙ₊₁ : (m : ℕ) → m ≤ suc n → A m → ⊥
  ¬minₙ₊₁ m m≤n+1 Aₘ with n≤m+1→n≤m∨n≡m+1 m≤n+1
  ¬minₙ₊₁ m m≤n+1 Aₘ | inj₁ m≤n = ¬minₙ m m≤n Aₘ
  ¬minₙ₊₁ m m≤n+1 Aₘ | inj₂ m≡n+1 = ¬Aₙ₊₁ (subst A m≡n+1 Aₘ)
min-Dec[ A ] (suc n) Dec[m≤n] | no ¬Aₙ₊₁ | (inj₂ (m , m≤n , Aₘ)) = inj₂ (m , ≤-suc m≤n , Aₘ)

------------------------------------------------------------------------

-- f : Baire → ℕ is Continuous if
-- ∀(α : Baire). ∃(n : ℕ).(∀(β : Baire). (α ≡⟪ n ⟫ β) → f α ≡ f β)

-- Continuity principle (every function f : Baire → ℕ is continuous)
-- ∀(f : Baire → ℕ).∀(α : Baire). ∃(n : ℕ).(∀(β : Baire). (α ≡⟪ n ⟫ β) → f α ≡ f β)

-- Uniform continuous
-- ∀(f : Cantor → ℕ).∃(n : ℕ).∀(α β : Cantor).(α ≡⟪ n ⟫ β) → f α ≡ f β


-- Main results:
-- The Curry-Howard interpretation of continuity principle is false.
--
-- This holds in topological topos
-- ∀(f : Baire → ℕ).∀(α : Baire). ∃(n : ℕ).(∀(β : Baire). (α ≡⟪ n ⟫ β) → f α ≡ f β)

-- This is also hold in topological topos
-- (α : Baire) → ∥ Σ[ n ∈ ℕ ] ((β : Baire) → (α ≡⟪ n ⟫ β) → f α ≡ f β) ∥

-- But this is not
-- (α : Baire) → Σ[ n ∈ ℕ ] ((β : Baire) → (α ≡⟪ n ⟫ β) → f α ≡ f β)

-- For uniform continuous, if assume function extensionality then the following are logically equivalent
-- (f : Cantor → ℕ) → Σ[ n ∈ ℕ ] ((α β : Cantor) → (α ≡⟪ n ⟫ β) → f α ≡ f β)
-- (f : Cantor → ℕ) → ∥ Σ[ n ∈ ℕ ] ((α β : Cantor) → (α ≡⟪ n ⟫ β) → f α ≡ f β) ∥

------------------------------------------------------------------------

continuous : (Baire → ℕ) → Set
continuous f = (α : Baire) → Σ[ n ∈ ℕ ] ((β : Baire) → (α ≡⟪ n ⟫ β) → f α ≡ f β)

Theorem1 : ((f : Baire → ℕ) → continuous f) → 0 ≡ 1
Theorem1 continuity = 0≡1
  where
------------------------------------------------------------------------
-- Main idea:
-- Use projection we can define function
  M : (Baire → ℕ) → ℕ
  M f = proj₁ (continuity f 0*)
-- 0* = 0,0,0,.....

  m : ℕ
  m = M (λ _ → 0)

-- And function
  f : Baire → ℕ
  f β = M (λ α → β (α m))
-- By continuity of f we can proof 0 ≡ 1
------------------------------------------------------------------------
  cont : (f : Baire → ℕ) (β : Baire) → 0* ≡⟪ M f ⟫ β → f 0* ≡ f β
  cont f = proj₂ (continuity f 0*)

  Observation₁ : f 0* ≡ m
  Observation₁ = refl

  Observation₂ : (β : Baire) → 0* ≡⟪ M f ⟫ β → m ≡ f β
  Observation₂ = cont f

  -- f β = M (λ α → β (α m))
  lemma₁ : ∀ β α → 0* ≡⟪ f β ⟫ α → β 0 ≡ β (α m)
  lemma₁ β α eq = cont (λ α → β (α m)) α eq

  β : Baire
  β = [0^ (M f) + 1 ][ 1 *]

  m≡fβ : m ≡ f β
  m≡fβ = Observation₂ β 0*≡⟪⟫[0^ M f +1][ 1 *]

  lemma₂ : ∀ α → 0* ≡⟪ m ⟫ α → β 0 ≡ β (α m)
  lemma₂ α eq = lemma₁ β α (subst (λ n → 0* ≡⟪ n ⟫ α) m≡fβ eq)

  α : Baire
  α = [0^ m ][ (M f) + 1 *]

  0≡1 : 0 ≡ 1
  0≡1 =  0
      ≡⟨ sym [0^ M f ][ 1 *]0≡0 ⟩
         (β 0)
      ≡⟨ lemma₂ α 0*≡⟪⟫[0^ m ][ M f + 1 *] ⟩
         (β (α m))
      ≡⟨ trans (cong β [0^ m ][ M f + 1 *]≡k)
               [0^ M f + 1 ][ 1 *]≡k ⟩
         1 ∎

------------------------------------------------------------------------

isProp : ∀ {ℓ} → Set ℓ → Set ℓ
isProp X = (x y : X) → x ≡ y

isSet : ∀ {ℓ} → Set ℓ → Set ℓ
isSet X = {x y : X} → isProp (x ≡ y)

Prop : ∀ {ℓ} → Set _
Prop {ℓ} = Σ[ X ∈ (Set ℓ) ] isProp X

module trunc where
  postulate
    ∥_∥ : ∀ {ℓ} → Set ℓ → Set ℓ
    ∣_∣ : ∀ {ℓ} {X : Set ℓ} → X → ∥ X ∥
    ∥_∥isProp : ∀ {ℓ} (X : Set ℓ) → isProp ∥ X ∥
    rec∥_∥ : ∀ {ℓ₁ ℓ₂} (X : Set ℓ₁) {P : Set ℓ₂} → isProp P → (X → P) → ∥ X ∥ → P

  -- usually we don't have ∥ X ∥ → X
  -- but for some type we have ∥ X ∥ → X
  ex₁ : ∥ 𝟘 ∥ → 𝟘
  ex₁ ∥𝟘∥ = rec∥ 𝟘 ∥ (λ ()) ⊥-elim ∥𝟘∥

  ex₂ : ∥ 𝟙 ∥ → 𝟙
  ex₂ ∥𝟙∥ = tt

  r : ∀ {ℓ} → Set ℓ → Prop
  r X = ∥ X ∥ , ∥ X ∥isProp

  s : ∀ {ℓ} → Prop → Set ℓ
  s (X , XisProp) = X

  r∘s≡ : ∀ {ℓ} {X : Set ℓ} → s(r(X)) ≡ ∥ X ∥
  r∘s≡ = refl

  module _ {ℓ} {ℓ'} {X : Set ℓ} where
    Σ' Π' : (X → Set ℓ') → Set _
    Σ' P = Σ[ x ∈ X ] (P x)
    Π' P = (x : X) → P x
  
    ∃' ∀' : (X → Prop) → Prop
    ∃' A = r (Σ' (s ∘ A))
    ∀' A = r (Π' (s ∘ A))

    _≤'_ : Prop {ℓ} → Prop {ℓ'} → Set _
    P ≤' Q = s(P) → s(Q)

    transpose_map : Prop {ℓ} → (X → Prop)
    transpose_map P = λ x → P

------------------------------------------------------------------------
-- Propositional truncation

-- isProp : ∀ {ℓ} → Set ℓ → Set ℓ
-- isProp X = (x y : X) → x ≡ y

-- isSet : ∀ {ℓ} → Set ℓ → Set ℓ
-- isSet X = {x y : X} → isProp (x ≡ y)

-- Prop : ∀ {ℓ} → Set _
-- Prop {ℓ} = Σ[ X ∈ (Set ℓ) ] isProp X

record ∥_∥ (X : Set) : Set₁ where
  field
    Ty : Set
    ∣_∣ : X → Ty
    TyisProp : isProp Ty
    rec : (P : Set) → isProp P → (X → P) → (Ty → P)

Lemma5 : {X Q : Set} → isProp Q → (X → Q) → (Q → X) → ∥ X ∥
Lemma5 {X} {Q} QisProp X→Q Q→X =
       record { Ty = Q ; ∣_∣ = X→Q
              ; TyisProp = QisProp
              ; rec = λ P PisProp X→P → X→P ∘ Q→X }

------------------------------------------------------------------------

Hedberg : ∀ {ℓ} {X : Set ℓ} → ((x y : X) → Dec (x ≡ y)) → isSet X
Hedberg {X = X} dec = XisSet
  where
  𝒇 : {x y : X} → x ≡ y → x ≡ y
  𝒇 {x} {y} p with dec x y
  𝒇 {x} {y} _ | yes p = p
  𝒇 {x} {y} p | no ¬p = p
  
  𝒇const : {x y : X} (p q : x ≡ y) → 𝒇 p ≡ 𝒇 q
  𝒇const {x} {y} p q with dec x y
  𝒇const {x} {y} _ _ | yes p = refl
  𝒇const {x} {y} _ q | no ¬p = ⊥-elim (¬p q)


  linv : {x y : X} → (p : x ≡ y) → trans p (sym p) ≡ refl
  linv refl = refl
  
  𝒇inv : {x y : X} → (p : x ≡ y) → trans (𝒇 p) (sym (𝒇 refl)) ≡ p
  𝒇inv refl = linv (𝒇 refl)

  XisSet : isSet X
  XisSet p q =  p
             ≡⟨ sym (𝒇inv p) ⟩
                trans (𝒇 p) (sym (𝒇 refl))
             ≡⟨ cong (λ r → trans r (sym (𝒇 refl))) (𝒇const p q) ⟩
                trans (𝒇 q) (sym (𝒇 refl))
             ≡⟨ 𝒇inv q ⟩
                q ∎

------------------------------------------------------------------------

funext : Set _
funext = {X : Set} {Y : X → Set} {f g : (x : X) → Y x} → (∀(x : X) → f x ≡ g x) → f ≡ g

------------------------------------------------------------------------
-- Theorem 3
-- Assume function extensionality then the following are logically equivalent
-- UC = (f : Cantor → ℕ) → Σ[ n ∈ ℕ ] ((α β : Cantor) → (α ≡⟪ n ⟫ β) → f α ≡ f β)
--      (f : Cantor → ℕ) → ∥ Σ[ n ∈ ℕ ] ((α β : Cantor) → (α ≡⟪ n ⟫ β) → f α ≡ f β) ∥

A : {f : Cantor → ℕ} →  ℕ → Set
A {f} n = (α β : Cantor) → α ≡⟪ n ⟫ β → f α ≡ f β

-- UC = (f : Cantor → ℕ) → Σ[ n ∈ ℕ ] (A {f} n)

-- Proof sketch
-- propositional truncation of Σ[ n ∈ ℕ ] (A n)
-- Σ[ k ∈ ℕ ] (A k) × ((i : ℕ) → A i → k ≤ i)
-- The minimum k such that A(k) is unique,
-- so this is a proposition.

-- ∥ Σ[ n ∈ ℕ ] (A n) ∥ →  Σ[ n ∈ ℕ ] (A n)
-- This is trivial since the minimum modulus is also a modulus
--
--
-- Σ[ n ∈ ℕ ] (A n)    →  ∥ Σ[ n ∈ ℕ ] (A n) ∥
-- A(n+1) implies A(n) is decidable,
-- because (s : 𝟚ⁿ). f(s0*) = f(s1*) is decidable.
-- So if A(n) then A(m) is decidable for m < n (lemma 4)
--
-- Bounded search for minimum m such that A(m) holds.
------------------------------------------------------------------------

Lemma4₁ : funext → (f : Cantor → ℕ) → (n : ℕ) → isProp (A {f} n)
Lemma4₁ funext f n = λ x y → funext (λ α → funext (λ β → funext (λ eq → ℕisSet _ _)))
        where
        ℕisSet : isSet ℕ
        ℕisSet = Hedberg ℕ-discrete

module Lemma4₂ (f : Cantor → ℕ) where
  Aₙ→Aₙ₊₁ : {n : ℕ} → A {f} n → A {f} (n + 1)
  Aₙ→Aₙ₊₁ {n} Aₙ α β eq = Aₙ α β ⟪ eq -1⟫

  ¬Aₙ₊₁→¬Aₙ : {n : ℕ} → ¬ (A {f} (n + 1)) → ¬ (A {f} n)
  ¬Aₙ₊₁→¬Aₙ {n} ¬Aₙ₊₁ = λ Aₙ → ¬Aₙ₊₁ (Aₙ→Aₙ₊₁ Aₙ)

  B : ℕ → Set
  B n = (s : Vec 𝟚 n) → f (s C∷ 0₂*) ≡ f (s C∷ 1₂*)

  Dec[Bₙ] : {n : ℕ} → Dec (B n)
  Dec[Bₙ] = Dec[Vec𝟚] _ (λ s → ℕ-discrete _ _)

  Aₙ→Bₙ : {n : ℕ} → A {f} n → B n
  Aₙ→Bₙ Aₙ = λ s → Aₙ (s C∷ 0₂*) (s C∷ 1₂*) (s∷≡⟪n⟫ s _ _)

  fα≡fβ : {n : ℕ} {Aₙ₊₁ : A (n + 1)}(α β : Cantor) → B n → (α ⟪ n ⟫) ≡ (β ⟪ n ⟫)
        → α n ≡ false → β n ≡ true → f α ≡ f β
  fα≡fβ {n} {Aₙ₊₁} α β Bₙ eq p q =
      f α
   ≡⟨ Aₙ₊₁ α ((α ⟪ n ⟫) C∷ 0₂*)
           (⟪_+1⟫_ {X = 𝟚} α≡⟪n⟫α[n]∷β (trans p (sym (α⟪n⟫∷β[n]≡β0 {n})))) ⟩
      f ((α ⟪ n ⟫) C∷ 0₂*)
   ≡⟨ cong (λ x → f (x C∷ 0₂*)) eq ⟩
      f ((β ⟪ n ⟫) C∷ 0₂*)
   ≡⟨ Bₙ (β ⟪ n ⟫) ⟩
      f ((β ⟪ n ⟫) C∷ 1₂*)
   ≡⟨ Aₙ₊₁ ((β ⟪ n ⟫) C∷ 1₂*) β
           (⟪_+1⟫_ {X = 𝟚} (sym α≡⟪n⟫α[n]∷β) (trans (α⟪n⟫∷β[n]≡β0 {n}) (sym q))) ⟩
      f β ∎

  Bₙ→Aₙ : {n : ℕ} {Aₙ₊₁ : A (n + 1)}→ B n → A {f} n
  Bₙ→Aₙ {n} {Aₙ₊₁} Bₙ α β eq with 𝟚-discrete (α n) (β n)
  Bₙ→Aₙ {n} {Aₙ₊₁} Bₙ α β eq | yes p = Aₙ₊₁ α β (⟪_+1⟫_ {X = 𝟚} eq p)
  Bₙ→Aₙ {n} {Aₙ₊₁} Bₙ α β eq | no ¬p with (𝟚≡T∨F (α n)) | (𝟚≡T∨F (β n))
  Bₙ→Aₙ {n} {Aₙ₊₁} Bₙ α β eq | no ¬p | (inj₁ αₙ≡T) | (inj₁ βₙ≡T) = ⊥-elim (¬p (trans αₙ≡T (sym βₙ≡T)))
  Bₙ→Aₙ {n} {Aₙ₊₁} Bₙ α β eq | no ¬p | (inj₁ αₙ≡T) | (inj₂ βₙ≡F) = sym (fα≡fβ {n} {Aₙ₊₁} β α Bₙ (sym eq) βₙ≡F αₙ≡T)
  Bₙ→Aₙ {n} {Aₙ₊₁} Bₙ α β eq | no ¬p | (inj₂ αₙ≡F) | (inj₁ βₙ≡T) = fα≡fβ {n} {Aₙ₊₁} α β Bₙ eq αₙ≡F βₙ≡T
  Bₙ→Aₙ {n} {Aₙ₊₁} Bₙ α β eq | no ¬p | (inj₂ αₙ≡F) | (inj₂ βₙ≡F) = ⊥-elim (¬p (trans αₙ≡F (sym βₙ≡F)))

  Dec[Bₙ]→Dec[Aₙ] : {n : ℕ} {Aₙ₊₁ : A {f} (n + 1)} → Dec (B n) → Dec (A {f} n)
  Dec[Bₙ]→Dec[Aₙ] {Aₙ₊₁ = Aₙ₊₁} (yes p) = yes (Bₙ→Aₙ {Aₙ₊₁ = Aₙ₊₁} p)
  Dec[Bₙ]→Dec[Aₙ] (no ¬p) = no (λ Aₙ → ¬p (Aₙ→Bₙ Aₙ))

  Aₙ₊₁→Dec[Aₙ] : {n : ℕ} → A {f} (n + 1) → Dec (A {f} n)
  Aₙ₊₁→Dec[Aₙ] {n} Aₙ₊₁ = Dec[Bₙ]→Dec[Aₙ] {Aₙ₊₁ = Aₙ₊₁} Dec[Bₙ]

  Lemma4₂ : (n : ℕ) → A {f} n
          → (m : ℕ) → m ≤ n → Dec (A {f} m)
  Lemma4₂ zero Aₙ .0 z≤n = yes (λ α β eq → Aₙ α β refl)
  Lemma4₂ (suc n) Aₙ m m≤n+1 with n≤m+1→n≤m∨n≡m+1 m≤n+1
  Lemma4₂ (suc n) Aₙ m m≤n+1 | inj₁ m≤n with Dec[Bₙ] {n}
  Lemma4₂ (suc n) Aₙ m m≤n+1 | inj₁ m≤n | (yes Bₙ) = Lemma4₂ n (Bₙ→Aₙ {Aₙ₊₁ = subst A sucn≡n+1 Aₙ} Bₙ) m m≤n
  Lemma4₂ (suc n) Aₙ m m≤n+1 | inj₁ m≤n | (no ¬Bₙ) = no (λ Aₙ → ¬Bₙ (λ s → Aₙ (s C∷ 0₂*) (s C∷ 1₂*) (s∷≡⟪m≤n⟫ s _ _ m≤n)))
  Lemma4₂ (suc n) Aₙ .(suc n) m≤n+1 | inj₂ refl = Aₙ₊₁→Dec[Aₙ] (Aₙ→Aₙ₊₁ Aₙ)


μ : {A : ℕ → Set} {k : ℕ} → Set
μ {A} {k} = (i : ℕ) → A i → k ≤ i

B : {A : ℕ → Set} (k : ℕ) → Set
B {A} k = A k × μ {A} {k}

∥Σ[ℕ]_∥ : (A : ℕ → Set) → Set
∥Σ[ℕ] A ∥  = Σ[ k ∈ ℕ ] B {A} k

k≤nisProp : {k n : ℕ} → isProp (k ≤ n)
k≤nisProp {zero} {zero} z≤n z≤n = refl
k≤nisProp {zero} {suc n} z≤n z≤n = refl
k≤nisProp {suc k} {zero} () k≤n₂
k≤nisProp {suc k} {suc n} (s≤s k≤n₁) (s≤s k≤n₂) = sym (cong s≤s (k≤nisProp k≤n₂ k≤n₁))

module Lemma6 (funext : funext) (A : ℕ → Set)
              (AisProp : (n : ℕ) → isProp (A n))
              (Aₙ→Dec[Aₘ] : ∀ n → A n → ∀ m → m ≤ n → Dec (A m)) where
  μisProp : {k : ℕ} → isProp (μ {A} {k})
  μisProp {k} = λ f g → funext (λ n → funext (λ Aₙ → k≤nisProp _ _))

  BₖisProp : {k : ℕ} → isProp (B {A} k)
  BₖisProp {k} (Aₖ₁ , μ₁) (Aₖ₂ , μ₂)
           with AisProp k Aₖ₁ Aₖ₂ | μisProp μ₁ μ₂
  ... | refl | refl = refl

  PisProp : isProp ∥Σ[ℕ] A ∥
  PisProp (k₁ , Aₖ₁ , μ₁) (k₂ , Aₖ₂ , μ₂)
          with m≤n∧n≤m→m=n (μ₁ k₂ Aₖ₂) (μ₂ k₁ Aₖ₁)
  PisProp (k₁ , Aₖ₁ , μ₁) (.k₁ , Aₖ₂ , μ₂) | refl
          with BₖisProp {k₁} (Aₖ₁ , μ₁) (Aₖ₂ , μ₂)
  ... | refl = refl

  Σ[n∈ℕ]Aₙ→∥Σ[ℕ]A∥ : Σ[ n ∈ ℕ ] (A n) → ∥Σ[ℕ] A ∥
  Σ[n∈ℕ]Aₙ→∥Σ[ℕ]A∥ (n , Aₙ) = sindℕ {C = λ n → A n → ∥Σ[ℕ] A ∥} istep n Aₙ
    where
    istep : (n : ℕ) → ((m : ℕ) → m < n → A m → ∥Σ[ℕ] A ∥) → A n → ∥Σ[ℕ] A ∥
    istep zero IH A₀ = 0 , A₀ , (λ i _ → z≤n)
    istep (suc n) IH Aₙ₊₁ with min-Dec[ A ] n (λ m m≤n → Aₙ→Dec[Aₘ] (suc n) Aₙ₊₁ m (≤-suc m≤n))
    istep (suc n) IH Aₙ₊₁ | inj₁ ¬minₙ = suc n , Aₙ₊₁ , (λ i Aᵢ → n≰m→m<n (λ i≰n → ¬minₙ i i≰n Aᵢ))
    istep (suc n) IH Aₙ₊₁ | inj₂ (m , m≤n , Aₘ) = IH m (s≤s m≤n) Aₘ
  
  ∥Σ[ℕ]A∥→Σ[n∈ℕ]Aₙ : ∥Σ[ℕ] A ∥ → Σ[ n ∈ ℕ ] (A n)
  ∥Σ[ℕ]A∥→Σ[n∈ℕ]Aₙ (k , Aₖ , _) = k , Aₖ

  ∥Σ[n∈ℕ]A∥ : ∥ Σ[ n ∈ ℕ ] (A n) ∥
  ∥Σ[n∈ℕ]A∥ = Lemma5 PisProp Σ[n∈ℕ]Aₙ→∥Σ[ℕ]A∥ ∥Σ[ℕ]A∥→Σ[n∈ℕ]Aₙ

module Theorem3 (funext : funext) where
  UC : Set
  UC = (f : Cantor → ℕ) → Σ[ n ∈ ℕ ] ((α β : Cantor) → (α ≡⟪ n ⟫ β) → f α ≡ f β)

  UC' : Set
  UC' = (f : Cantor → ℕ) → ∥Σ[ℕ] (λ n → ((α β : Cantor) → (α ≡⟪ n ⟫ β) → f α ≡ f β)) ∥

  UC→UC' : UC → UC'
  UC→UC' uc f = Σ[n∈ℕ]Aₙ→∥Σ[ℕ]A∥ (uc f)
    where
    module lemma4 = Lemma4₂ f
    open lemma4
    module lemma6 = Lemma6 funext (A {f}) (Lemma4₁ funext f) Lemma4₂
    open lemma6


  UC'→UC : UC' → UC
  UC'→UC uc' f = ∥Σ[ℕ]A∥→Σ[n∈ℕ]Aₙ (uc' f)
    where
    module lemma4 = Lemma4₂ f
    open lemma4
    module lemma6 = Lemma6 funext (A {f}) (Lemma4₁ funext f) Lemma4₂
    open lemma6
