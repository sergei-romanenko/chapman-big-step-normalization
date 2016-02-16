module FiniteProducts.StructuralNormaliser where

open import FiniteProducts.Utils
open import FiniteProducts.Syntax
open import FiniteProducts.Conversion
open import FiniteProducts.OPE
open import FiniteProducts.OPELemmas
open import FiniteProducts.BigStepSemantics
open import FiniteProducts.StrongComputability


--
-- Structurally recursive evaluator.
--

mutual

  infix 4 ⟦_⟧_&_ ⟦_⟧*_&_
  infixl 5 _⟨∙⟩_&_

  ⟦_⟧_&_ : ∀ {α Γ Δ} (t : Tm Δ α) (ρ : Env Γ Δ) {w} →
    (⇓w : ⟦ t ⟧ ρ ⇓ w) → ∃ λ w′ → w′ ≡ w

  ⟦ ø ⟧ u ∷ ρ & ø⇓ =
    u , refl
  ⟦ t ∙ t′ ⟧ ρ & ∙⇓ ⇓u ⇓v ⇓w
    with ⟦ t ⟧ ρ & ⇓u | ⟦ t′ ⟧ ρ & ⇓v
  ... | u , refl | v , refl = u ⟨∙⟩ v & ⇓w
  ⟦ ƛ t ⟧ ρ & ƛ⇓ =
    lam t ρ , refl
  ⟦ t [ σ ] ⟧ ρ & []⇓ ⇓θ ⇓w
    with ⟦ σ ⟧* ρ & ⇓θ
  ... | θ , refl = ⟦ t ⟧ θ & ⇓w
  ⟦ void ⟧ ρ & void⇓ =
    void , refl
  ⟦ pair ta tb ⟧ ρ & pair⇓ ⇓u ⇓v
    with ⟦ ta ⟧ ρ & ⇓u | ⟦ tb ⟧ ρ & ⇓v
  ... | u , refl | v , refl
    = pair u v , refl
  ⟦ fst t ⟧ ρ & fst⇓ ⇓uv ⇓w
    with ⟦ t ⟧ ρ & ⇓uv
  ... | uv , refl
    with fst⟦ uv ⟧& ⇓w
  ... | u , refl
    = u , refl
  ⟦ snd t ⟧ ρ & snd⇓ ⇓uv ⇓w
    with ⟦ t ⟧ ρ & ⇓uv
  ... | uv , refl
    with snd⟦ uv ⟧& ⇓w
  ... | v , refl
    = v , refl

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

  fst⟦_⟧& : ∀ {α β Γ} (uv : Val Γ (α * β)) {w}
    (⇓w : Fst uv ⇓ w) → ∃ λ w′ → w′ ≡ w
  fst⟦_⟧& (ne us) fst-ne⇓ =
    ne (fst us) , refl
  fst⟦_⟧& (pair u v) fst-pair⇓ =
    u , refl

  snd⟦_⟧& : ∀ {α β Γ} (uv : Val Γ (α * β)) {w}
    (⇓w : Snd uv ⇓ w) → ∃ λ w′ → w′ ≡ w
  snd⟦_⟧& (ne us) snd-ne⇓ =
    ne (snd us) , refl
  snd⟦_⟧& (pair u v) snd-pair⇓ =
    v , refl

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
  ⌜_&_⌝ {One} u One⇓ =
    void , refl
  ⌜_&_⌝ {α * β} uv (Prod⇓ ⇓u ⇓nu ⇓v ⇓nv)
    with fst⟦ uv ⟧& ⇓u | snd⟦ uv ⟧& ⇓v
  ... | u , refl | v , refl
    with ⌜ u & ⇓nu ⌝ | ⌜ v & ⇓nv ⌝
  ... | nu , refl | nv , refl
    = pair nu nv , refl

  ⌜_&_⌝* : ∀ {α Γ} (us : NeVal Γ α) {ns} (⇓ns : Quote* us ⇓ ns) →
    ∃ λ ns′ → ns′ ≡ ns
  ⌜ var x & var⇓ ⌝* =
    var x , refl
  ⌜ app us u & app⇓ ⇓ns ⇓n ⌝*
    with ⌜ us & ⇓ns ⌝* | ⌜ u & ⇓n ⌝
  ... | ns′ , refl | n′ , refl
    = app ns′ n′ , refl
  ⌜ fst us & fst⇓ ⇓ns ⌝*
    with ⌜ us & ⇓ns ⌝*
  ... | ns , refl
    = fst ns , refl
  ⌜ snd us & snd⇓ ⇓ns ⌝*
    with ⌜ us & ⇓ns ⌝*
  ... | ns , refl
    = snd ns , refl

--
-- Normalizer!
--

nf_&_ : ∀ {α Γ} (t : Tm Γ α) {n} (⇓n : Nf t ⇓ n) →
  ∃ λ n′ → n′ ≡ n
nf t & nf⇓ ⇓u ⇓n
  with ⟦ t ⟧ id-env & ⇓u
... | u′ , refl
  with ⌜ u′ & ⇓n ⌝
... | n′ , refl
  = n′ , refl

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

