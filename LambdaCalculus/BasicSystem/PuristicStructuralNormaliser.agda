module BasicSystem.PuristicStructuralNormaliser where

open import BasicSystem.Utils
open import BasicSystem.Syntax
open import BasicSystem.Conversion
open import BasicSystem.OPE
open import BasicSystem.OPELemmas
open import BasicSystem.BigStepSemantics
open import BasicSystem.StrongComputability

--
-- This version of structurally recursive evaluator,
-- as compared to the one in `BasicSystem.StructuralNormaliser`,
-- is written in more "puristic" style, in order for
-- "computation" and "logic" to be more explicitly separated.
-- Now pattern matching against proofs is made in auxiliary functions that
-- consider a single case. Hence, proofs are not used for making decisions.

mutual

  infix 4 ⟦_⟧_&_ ⟦_⟧*_&_
  infixl 5 _⟨∙⟩_&_

  ⟦_⟧_&_ : ∀ {α Γ Δ} (t : Tm Δ α) (ρ : Env Γ Δ)
    {w} (⇓w : ⟦ t ⟧ ρ ⇓ w) → ∃ λ w′ → w′ ≡ w

  ⟦ ø ⟧ u ∷ ρ & ⇓w =
    ⟦ø⟧ u ρ ⇓w
  ⟦ f ∙ a ⟧ ρ & ⇓w =
    ⟦∙⟧ f a ρ ⇓w
  ⟦ ƛ t ⟧ ρ & ⇓w =
    ⟦ƛ⟧ t ρ ⇓w
  ⟦ t [ σ ] ⟧ ρ & ⇓w =
    ⟦[]⟧ t σ ρ ⇓w

  ⟦∙⟧ : ∀ {α β Γ Δ} (f : Tm Δ (α ⇒ β)) (a : Tm Δ α) (ρ : Env Γ Δ)
    {w} (⇓w : ⟦ f ∙ a ⟧ ρ ⇓ w) → ∃ λ w′ → w′ ≡ w
  ⟦∙⟧ f a ρ (∙⇓ ⇓u ⇓v ⇓w)
    with ⟦ f ⟧ ρ & ⇓u | ⟦ a ⟧ ρ & ⇓v
  ... | u , refl | v , refl
    = u ⟨∙⟩ v & ⇓w

  ⟦ø⟧ : ∀ {α Γ Δ} (u : Val Γ α) (ρ : Env Γ Δ)
    {w} (⇓w : ⟦ ø ⟧ u ∷ ρ ⇓ w) → ∃ λ w′ → w′ ≡ w
  ⟦ø⟧ u ρ ø⇓ =
    u , refl

  ⟦ƛ⟧ : ∀ {α β Γ Δ} (t : Tm (α ∷ Δ) β) (ρ : Env Γ Δ)
    {w} (⇓w : ⟦ ƛ t ⟧ ρ ⇓ w) → ∃ λ w′ → w′ ≡ w
  ⟦ƛ⟧ t ρ ƛ⇓ =
    lam t ρ , refl

  ⟦[]⟧ : ∀ {α Γ Δ Δ′} (t : Tm Δ′ α) (σ : Sub Δ Δ′) (ρ : Env Γ Δ)
    {w} (⇓w : ⟦ t [ σ ] ⟧ ρ ⇓ w) → ∃ λ w′ → w′ ≡ w
  ⟦[]⟧ t σ ρ ([]⇓ ⇓θ ⇓w)
    with ⟦ σ ⟧* ρ & ⇓θ
  ... | θ , refl
    = ⟦ t ⟧ θ & ⇓w

  _⟨∙⟩_&_ : ∀ {α β Γ} (u : Val Γ (α ⇒ β)) (v : Val Γ α)
    {w} (⇓w : u ⟨∙⟩ v ⇓ w) → ∃ λ w′ → w′ ≡ w
  ne us ⟨∙⟩ u & ⇓w =
    ne⟨∙⟩ us u ⇓w
  lam t ρ ⟨∙⟩ u & ⇓w =
    lam⟨∙⟩ t ρ u ⇓w

  ne⟨∙⟩ : ∀ {α β Γ} (us : NeVal Γ (α ⇒ β)) (u : Val Γ α)
    {w} (⇓w : ne us ⟨∙⟩ u ⇓ w) → ∃ (λ w′ → w′ ≡ w)
  ne⟨∙⟩ us u ne⇓ =
    ne (app us u) , refl

  lam⟨∙⟩ : ∀ {α β Γ Δ} (t : Tm (α ∷ Δ) β) (ρ : Env Γ Δ) (u : Val Γ α)
    {w} (⇓w : lam t ρ ⟨∙⟩ u ⇓ w) → ∃ (λ w′ → w′ ≡ w)
  lam⟨∙⟩ t ρ u (lam⇓ ⇓w′) =
    ⟦ t ⟧ (u ∷ ρ) & ⇓w′

  ⟦_⟧*_&_ : ∀ {Β Γ Δ} (σ : Sub Γ Δ) (ρ : Env Β Γ)
    {θ : Env Β Δ} (⇓θ : ⟦ σ ⟧* ρ ⇓ θ) →
    ∃ λ φ → φ ≡ θ

  ⟦ ı ⟧* ρ & ⇓θ =
    ⟦ı⟧* ρ ⇓θ
  ⟦ σ₁ ○ σ₂ ⟧* ρ & ⇓θ =
    ⟦○⟧* σ₁ σ₂ ρ ⇓θ
  ⟦ t ∷ σ ⟧* ρ & ⇓θ =
    ⟦∷⟧* t σ ρ ⇓θ
  ⟦ ↑ ⟧* u ∷ ρ & ⇓θ =
    ⟦↑⟧* u ρ ⇓θ

  ⟦ı⟧* : ∀ {Β Γ} (ρ : Env Β Γ)
    {θ} (⇓θ : ⟦ ı ⟧* ρ ⇓ θ ) → ∃ λ φ → φ ≡ θ
  ⟦ı⟧* ρ ι⇓ =
    ρ , refl

  ⟦○⟧* : ∀ {Β Γ Δ Δ′} (σ₁ : Sub Δ′ Δ) (σ₂ : Sub Γ Δ′) (ρ : Env Β Γ)
    {θ} (⇓θ : ⟦ σ₁ ○ σ₂ ⟧* ρ ⇓ θ) → ∃ λ φ → φ ≡ θ
  ⟦○⟧* σ₁ σ₂ ρ (○⇓ ⇓θ ⇓φ)
    with ⟦ σ₂ ⟧* ρ & ⇓θ
  ... | θ , refl =
    ⟦ σ₁ ⟧* θ & ⇓φ

  ⟦∷⟧* : ∀ {α Β Γ Δ} (t : Tm Γ α) (σ : Sub Γ Δ) (ρ : Env Β Γ)
    {θ} (⇓θ : ⟦ t ∷ σ ⟧* ρ ⇓ θ) → ∃ λ φ → φ ≡ θ
  ⟦∷⟧* t σ ρ (∷⇓ ⇓u ⇓θ)
    with ⟦ t ⟧ ρ & ⇓u | ⟦ σ ⟧* ρ & ⇓θ
  ... | u , refl | θ , refl
    = u ∷ θ , refl

  ⟦↑⟧* : ∀ {α Γ Δ} (u : Val Γ α) (ρ : Env Γ Δ)
    {θ} (⇓θ : ⟦ ↑ ⟧* u ∷ ρ ⇓ θ) → ∃ λ φ → φ ≡ θ
  ⟦↑⟧* u ρ ↑⇓ =
    ρ , refl

mutual

  infix 4 ⌜_&_⌝ ⌜_&_⌝*

  ⌜_&_⌝ : ∀ {α Γ} (u : Val Γ α) {n} (⇓n : Quote u ⇓ n) →
    ∃ λ n′ → n′ ≡ n
  ⌜_&_⌝ {⋆} {Γ} (ne us) {n} ⇓n =
    ⌜⋆⌝ us ⇓n
  ⌜_&_⌝ {α ⇒ β} {Γ} f ⇓n =
    ⌜⇒⌝ f ⇓n

  ⌜⋆⌝  : ∀ {Γ} (us : NeVal Γ ⋆) {n} (⇓n : Quote ne us ⇓ n) →
    ∃ λ n′ → n′ ≡ n
  ⌜⋆⌝ us (⋆⇓ .us ⇓ns)
    with ⌜ us & ⇓ns ⌝*
  ... | ns , refl
    = ne⋆ ns , refl

  ⌜⇒⌝ : ∀ {α β Γ} (f : Val Γ (α ⇒ β)) {n } (⇓n : Quote f ⇓ n) →
    ∃ λ n′ → n′ ≡ n
  ⌜⇒⌝ f (⇒⇓ ⇓u ⇓n)
    with val≤ wk f ⟨∙⟩ ne (var zero) & ⇓u
  ... | u , refl
    with ⌜ u  & ⇓n ⌝
  ... | n , refl
    = lam n , refl

  ⌜_&_⌝* : ∀ {α Γ} (us : NeVal Γ α) {ns} (⇓ns : Quote* us ⇓ ns) →
    ∃ λ ns′ → ns′ ≡ ns
  ⌜ var x & ⇓ns ⌝* =
    ⌜var⌝* x ⇓ns
  ⌜ app us u & ⇓ns ⌝* =
    ⌜app⌝* us u ⇓ns

  ⌜var⌝* : ∀ {α Γ} (x : Var Γ α) {ns} (⇓ns : Quote* var x ⇓ ns) →
    ∃ λ ns′ → ns′ ≡ ns
  ⌜var⌝* x var⇓ =
    var x , refl

  ⌜app⌝* : ∀ {α β Γ} (us : NeVal Γ (α ⇒ β)) (u : Val Γ α)
    {ns} (⇓ns : Quote* app us u ⇓ ns) → ∃ λ ns′ → ns′ ≡ ns
  ⌜app⌝* us u (app⇓ ⇓ns ⇓n)
    with ⌜ us & ⇓ns ⌝* | ⌜ u & ⇓n ⌝
  ... | ns′ , refl | n′ , refl
    = app ns′ n′ , refl

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

