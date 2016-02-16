module FiniteProducts.OPEBigStep where

open import FiniteProducts.Utils
open import FiniteProducts.Syntax
open import FiniteProducts.Conversion
open import FiniteProducts.OPE
open import FiniteProducts.OPELemmas
open import FiniteProducts.BigStepSemantics


--
-- OPEs commute with evaluation
--

mutual

  ⟦⟧⇓≤ : ∀ {α Β Γ Δ} (η : Β ≤ Γ) {t : Tm Δ α} {ρ : Env Γ Δ} {u : Val Γ α}
    (⇓u : ⟦ t ⟧ ρ ⇓ u) →
    ⟦ t ⟧ env≤ η ρ ⇓ val≤ η u
  ⟦⟧⇓≤ η ø⇓ = ø⇓
  ⟦⟧⇓≤ η (∙⇓ ⇓u ⇓v ⇓w) = ∙⇓ (⟦⟧⇓≤ η ⇓u) (⟦⟧⇓≤ η ⇓v) (⟨∙⟩⇓≤ η ⇓w)
  ⟦⟧⇓≤ η ƛ⇓ = ƛ⇓
  ⟦⟧⇓≤ η ([]⇓ ⇓θ ⇓u) = []⇓ (⟦⟧*⇓≤ η ⇓θ) (⟦⟧⇓≤ η ⇓u)
  ⟦⟧⇓≤ η void⇓ = void⇓
  ⟦⟧⇓≤ η (pair⇓ ⇓u ⇓v) =
    pair⇓ (⟦⟧⇓≤ η ⇓u) (⟦⟧⇓≤ η ⇓v)
  ⟦⟧⇓≤ η (fst⇓ ⇓uv ⇓w) =
    fst⇓ (⟦⟧⇓≤ η ⇓uv) (fst⇓≤ η ⇓w)
  ⟦⟧⇓≤ η (snd⇓ ⇓uv ⇓w) =
    snd⇓ (⟦⟧⇓≤ η ⇓uv) (snd⇓≤ η ⇓w)

  ⟦⟧*⇓≤ : ∀ {Β Γ Δ Δ′} (η : Β ≤ Γ) {σ : Sub Δ′ Δ} {ρ : Env Γ Δ′} {θ : Env Γ Δ}
    (⇓θ : ⟦ σ ⟧* ρ ⇓ θ) →
    ⟦ σ ⟧* env≤ η ρ ⇓ env≤ η θ
  ⟦⟧*⇓≤ η ι⇓ = ι⇓
  ⟦⟧*⇓≤ η (○⇓ ⇓θ₁ ⇓θ₂) = ○⇓ (⟦⟧*⇓≤ η ⇓θ₁) (⟦⟧*⇓≤ η ⇓θ₂)
  ⟦⟧*⇓≤ η (∷⇓ ⇓u ⇓θ) = ∷⇓ (⟦⟧⇓≤ η ⇓u) (⟦⟧*⇓≤ η ⇓θ)
  ⟦⟧*⇓≤ η ↑⇓ = ↑⇓

  ⟨∙⟩⇓≤ : ∀ {α β Β Γ} (η : Β ≤ Γ)
    {u : Val Γ (α ⇒ β)} {v : Val Γ α} {w : Val Γ β}
    (⇓w : u ⟨∙⟩ v ⇓ w) →
    val≤ η u ⟨∙⟩ val≤ η v ⇓ val≤ η w
  ⟨∙⟩⇓≤ η ne⇓ = ne⇓
  ⟨∙⟩⇓≤ η (lam⇓ ⇓v) = lam⇓ (⟦⟧⇓≤ η ⇓v)

  fst⇓≤ : ∀ {α β Β Γ} (η : Β ≤ Γ) {uv : Val Γ (α * β)} {w}
    (⇓w : Fst uv ⇓ w) → Fst val≤ η uv ⇓ val≤ η w
  fst⇓≤ η fst-pair⇓ = fst-pair⇓
  fst⇓≤ η fst-ne⇓ = fst-ne⇓

  snd⇓≤ : ∀ {α β Β Γ} (η : Β ≤ Γ) {uv : Val Γ (α * β)} {w}
    (⇓w : Snd uv ⇓ w) → Snd val≤ η uv ⇓ val≤ η w
  snd⇓≤ η snd-pair⇓ = snd-pair⇓
  snd⇓≤ η snd-ne⇓ = snd-ne⇓

mutual

  quote≤ : ∀ {α Β Γ} (η : Β ≤ Γ) {u : Val Γ α} {n : Nf Γ α}
    (⇓n : Quote u ⇓ n) →
      Quote val≤ η u ⇓ nf≤ η n

  quote≤ η (⋆⇓ us ⇓ns) =
    ⋆⇓ (neVal≤ η us) (quote*≤ η ⇓ns)
  quote≤ η (⇒⇓ {f = f} {u} {n} ⇓u ⇓n) =
    ⇒⇓ ⇓u′′′ ⇓n′
    where
      ⇓u′ : val≤ (≤lift η) (val≤ wk f) ⟨∙⟩ ne (var zero) ⇓ val≤ (≤lift η) u
      ⇓u′ = ⟨∙⟩⇓≤ (≤lift η) ⇓u
      ⇓u′′′ : val≤ wk (val≤ η f) ⟨∙⟩ ne (var zero) ⇓ val≤ (≤lift η) u
      ⇓u′′′ = subst (λ w → w ⟨∙⟩ ne (var zero) ⇓ val≤ (≤lift η) u)
                    (sym $ wk∘val≤ η f) ⇓u′
      ⇓n′ : Quote val≤ (≤lift η) u ⇓ nf≤ (≤lift η) n
      ⇓n′ = quote≤ (≤lift η) ⇓n
  quote≤ η One⇓ = One⇓
  quote≤ η (Prod⇓ ⇓u ⇓na ⇓v ⇓nb) =
    Prod⇓ (fst⇓≤ η ⇓u) (quote≤ η ⇓na) (snd⇓≤ η ⇓v) (quote≤ η ⇓nb)

  quote*≤ : ∀ {α Β Γ} (η : Β ≤ Γ) {us : NeVal Γ α} {ns : NeNf Γ α}
    (⇓ns : Quote* us ⇓ ns) →
      Quote* neVal≤ η us ⇓ neNf≤ η ns

  quote*≤ η var⇓ = var⇓
  quote*≤ η (app⇓ ⇓ns ⇓n) =
    app⇓ (quote*≤ η ⇓ns) (quote≤ η ⇓n)
  quote*≤ η (fst⇓ ⇓ns) =
    fst⇓ (quote*≤ η ⇓ns)
  quote*≤ η (snd⇓ ⇓ns) =
    snd⇓ (quote*≤ η ⇓ns)

-- embNeVal (neVal≤ η us) ≈ embNeNf (neNf≤ η ns)

embNe≤≈ : ∀ {α Β Γ} (η : Β ≤ Γ) (us : NeVal Γ α) (ns : NeNf Γ α) →
  (p : embNeVal us ≈ embNeNf ns) →
     embNeVal (neVal≤ η us) ≈ embNeNf (neNf≤ η ns)
embNe≤≈ η us ns p = begin
  embNeVal (neVal≤ η us)
    ≈⟨ embNeVal∘≤ η us ⟩
  embNeVal us [ ≤2sub η ]
    ≈⟨ ≈cong[] p ≈≈refl ⟩
  embNeNf ns [ ≤2sub η ]
    ≈⟨ ≈sym (embNeNf∘≤ η ns) ⟩
  embNeNf (neNf≤ η ns)
  ∎
  where open ≈-Reasoning

-- fst (embVal u) ≈ embVal w

fst∘embVal≈ : ∀ {α β Γ} {u : Val Γ (α * β)} {w}
  (⇓w : Fst u ⇓ w) → fst (embVal u) ≈ embVal w
fst∘embVal≈ fst-pair⇓ = ≈βfst
fst∘embVal≈ fst-ne⇓ = ≈refl

-- snd (embVal u) ≈ embVal w

snd∘embVal≈ : ∀ {α β Γ} {u : Val Γ (α * β)} {w}
  (⇓w : Snd u ⇓ w) → snd (embVal u) ≈ embVal w
snd∘embVal≈ snd-pair⇓ = ≈βsnd
snd∘embVal≈ snd-ne⇓ = ≈refl

