module NaturalNumbers.StructuralNormaliser where

open import NaturalNumbers.Utils
open import NaturalNumbers.Syntax
open import NaturalNumbers.Conversion
open import NaturalNumbers.OPE
open import NaturalNumbers.OPELemmas
open import NaturalNumbers.BigStepSemantics
open import NaturalNumbers.StrongComputability


--
-- Structurally recursive evaluator.
--

mutual

  infix 4 ⟦_⟧_&_ ⟦_⟧*_&_
  infixl 5 _⟨∙⟩_&_

  ⟦_⟧_&_ : ∀ {α Γ Δ} (t : Tm Δ α) (ρ : Env Γ Δ) {w : Val Γ α} →
    ⟦ t ⟧ ρ ⇓ w → ∃ λ w′ → w′ ≡ w

  ⟦ ø ⟧ u ∷ ρ & ø⇓ =
    u , refl
  ⟦ t ∙ t′ ⟧ ρ & ∙⇓ ⇓u ⇓v ⇓w
    with ⟦ t ⟧ ρ & ⇓u | ⟦ t′ ⟧ ρ & ⇓v
  ... | u , refl | v , refl
    = u ⟨∙⟩ v & ⇓w
  ⟦ ƛ t ⟧ ρ & ƛ⇓ =
    lam t ρ , refl
  ⟦ t [ σ ] ⟧ ρ & []⇓ ⇓θ ⇓w
    with ⟦ σ ⟧* ρ & ⇓θ
  ... | θ , refl
    = ⟦ t ⟧ θ & ⇓w
  ⟦ zero ⟧ ρ & zero⇓ =
    zero , refl
  ⟦ suc t ⟧ ρ & suc⇓ ⇓w
    with ⟦ t ⟧ ρ & ⇓w
  ... | u , refl
    = suc u , refl
  ⟦ prim a b k ⟧ ρ & prim⇓ ⇓u ⇓v ⇓w ⇓w′
    with ⟦ a ⟧ ρ & ⇓u | ⟦ b ⟧ ρ & ⇓v | ⟦ k ⟧ ρ & ⇓w
  ... | u , refl | v , refl | w , refl
    = prim⟦⟧ u v w ⇓w′

  ⟦_⟧*_&_ : ∀ {B Γ Δ} (σ : Sub Γ Δ) (ρ : Env B Γ) {θ : Env B Δ} →
    ⟦ σ ⟧* ρ ⇓ θ → ∃ λ φ → φ ≡ θ

  ⟦ ı ⟧* ρ & ι⇓ =
    ρ , refl
  ⟦ σ₁ ○ σ₂ ⟧* ρ & ○⇓ ⇓θ ⇓φ
    with ⟦ σ₂ ⟧* ρ & ⇓θ
  ... | θ , refl =
    ⟦ σ₁ ⟧* θ & ⇓φ
  ⟦ t ∷ σ ⟧* ρ & ∷⇓ ⇓u ⇓θ
    with ⟦ t ⟧ ρ & ⇓u | ⟦ σ ⟧* ρ & ⇓θ
  ... | u , refl | θ , refl =
    u ∷ θ , refl
  ⟦ ↑ ⟧* u ∷ ρ & ↑⇓ =
    ρ , refl

  _⟨∙⟩_&_ : ∀ {α β Γ} (u : Val Γ (α ⇒ β)) (v : Val Γ α) {w : Val Γ β} →
    u ⟨∙⟩ v ⇓ w → ∃ λ w′ → w′ ≡ w

  ne us ⟨∙⟩ u & ne⇓ =
    ne (app us u) , refl
  lam t ρ ⟨∙⟩ u & lam⇓ ⇓w =
    ⟦ t ⟧ (u ∷ ρ) & ⇓w

  prim⟦⟧ : ∀ {α Γ} (u : Val Γ α) (v : Val Γ (N ⇒ α ⇒ α)) (w : Val Γ N)
    {z} (⇓z : Prim u & v & w ⇓ z) →
    ∃ λ z′ → z′ ≡ z

  prim⟦⟧ u v (ne us) primn⇓ =
    ne (prim u v us) , refl
  prim⟦⟧ u v zero primz⇓ =
    u , refl
  prim⟦⟧ u v (suc w) (prims⇓ ⇓vw ⇓z ⇓vwz)
    with v ⟨∙⟩ w & ⇓vw | prim⟦⟧ u v w ⇓z
  ... | vw , refl | z , refl
    = vw ⟨∙⟩ z & ⇓vwz


mutual

  infix 4 ⌜_&_⌝ ⌜_&_⌝*

  ⌜_&_⌝ : ∀ {α Γ} (u : Val Γ α) {n} (⇓n : Quote u ⇓ n) →
    ∃ λ n′ → n′ ≡ n
  ⌜_&_⌝ {⋆} (ne us) (⋆⇓ .us ⇓ns)
    with ⌜ us & ⇓ns ⌝*
  ... | ns′ , refl
    = ne⋆ ns′ , refl
  ⌜_&_⌝ {α ⇒ β} f (⇒⇓ ⇓u ⇓n)
    with val≤ wk f ⟨∙⟩ ne (var zero) & ⇓u
  ... | u′ , refl
    with ⌜ u′  & ⇓n ⌝
  ... | n′ , refl
    = lam n′ , refl
  ⌜_&_⌝ {N} (ne us) (N⇓ ⇓ns)
    with ⌜ us & ⇓ns ⌝*
  ... | ns , refl
    = neN ns , refl
  ⌜_&_⌝ {N} zero zero⇓ =
    zero , refl
  ⌜_&_⌝ {N} (suc u) (suc⇓ ⇓n)
    with ⌜ u & ⇓n ⌝
  ... | n , refl
    = suc n , refl

  ⌜_&_⌝* : ∀ {α Γ} (us : NeVal Γ α) {ns} (⇓ns : Quote* us ⇓ ns) →
    ∃ λ ns′ → ns′ ≡ ns
  ⌜ var x & var⇓ ⌝* =
    var x , refl
  ⌜ app us u & app⇓ ⇓ns ⇓n ⌝*
    with ⌜ us & ⇓ns ⌝* | ⌜ u & ⇓n ⌝
  ... | ns′ , refl | n′ , refl
    = app ns′ n′ , refl
  ⌜ prim u v us & prim⇓ ⇓nu ⇓nv ⇓ns ⌝*
    with ⌜ u & ⇓nu ⌝ | ⌜ v & ⇓nv ⌝ | ⌜ us & ⇓ns ⌝*
  ... | nu , refl | nv , refl | ns , refl
    = prim nu nv ns , refl

--
-- Normalizer!
--

nf_&_ : ∀ {α Γ} (t : Tm Γ α) {n} (⇓n : Nf t ⇓ n) →
  ∃ λ n′ → n′ ≡ n
nf t & nf⇓ ⇓u ⇓n
  with ⟦ t ⟧ id-env & ⇓u
... | u , refl
  with ⌜ u & ⇓n ⌝
... | n , refl
  = n , refl

nf : ∀ {α Γ} (t : Tm Γ α) → Nf Γ α
nf t
  with all-scv t id-env sce-id-env
... | u , p , ⇓u , ≈u
  with all-quote u p
... | n , ⇓n , ≈n
  with nf t & nf⇓ ⇓u ⇓n
... | n′ , n′≡n
  = n′

--
-- This holds "by construction":
--     Nf t ⇓ n → nf t ≡ n
--

-- Nf t ⇓ n → nf t ≡ n

nf⇓→nf : ∀ {α Γ} (t : Tm Γ α) {n} (⇓n : Nf t ⇓ n) → nf t ≡ n
nf⇓→nf t {n} (nf⇓ {u = u} ⇓u ⇓n)
  with all-scv t id-env sce-id-env
... | u′ , p′ , ⇓u′ , ≈u′
  with all-quote u′ p′
... | n′ , ⇓n′ , ≈n′
  with nf t & nf⇓ ⇓u′ ⇓n′
... | n′′ , n′′≡n′ rewrite n′′≡n′
  = quote⇓-det ⇓n′ ⇓n (⟦⟧⇓-det ⇓u′ ⇓u refl)

