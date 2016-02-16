module NaturalNumbers.OPEBigStep where

open import NaturalNumbers.Utils
open import NaturalNumbers.Syntax
open import NaturalNumbers.Conversion
open import NaturalNumbers.OPE
open import NaturalNumbers.OPELemmas
open import NaturalNumbers.BigStepSemantics


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
  ⟦⟧⇓≤ η zero⇓ = zero⇓
  ⟦⟧⇓≤ η (suc⇓ ⇓u) = suc⇓ (⟦⟧⇓≤ η ⇓u)
  ⟦⟧⇓≤ η (prim⇓ ⇓u ⇓v ⇓w ⇓w′) =
    prim⇓ (⟦⟧⇓≤ η ⇓u) (⟦⟧⇓≤ η ⇓v) (⟦⟧⇓≤ η ⇓w) (prim⇓≤ η ⇓w′)

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

  prim⇓≤ : ∀ {α Β Γ} (η : Β ≤ Γ)
    {u : Val Γ α} {v : Val Γ (N ⇒ α ⇒ α)} {w : Val Γ N} {w′ : Val Γ α}
    (⇓w′ : Prim u & v & w ⇓ w′) →
    Prim val≤ η u & val≤ η v & val≤ η w ⇓ val≤ η w′
  prim⇓≤ η primn⇓ = primn⇓
  prim⇓≤ η primz⇓ = primz⇓
  prim⇓≤ η (prims⇓ ⇓vw ⇓w′ ⇓vww′) =
    prims⇓ (⟨∙⟩⇓≤ η ⇓vw) (prim⇓≤ η ⇓w′) (⟨∙⟩⇓≤ η ⇓vww′)

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
  quote≤ η (N⇓ ⇓ns) =
    N⇓ (quote*≤ η ⇓ns)
  quote≤ η zero⇓ =
    zero⇓
  quote≤ η (suc⇓ ⇓n) =
    suc⇓ (quote≤ η ⇓n)

  quote*≤ : ∀ {α Β Γ} (η : Β ≤ Γ) {us : NeVal Γ α} {ns : NeNf Γ α}
    (⇓ns : Quote* us ⇓ ns) →
      Quote* neVal≤ η us ⇓ neNf≤ η ns

  quote*≤ η var⇓ = var⇓
  quote*≤ η (app⇓ ⇓ns ⇓n) =
    app⇓ (quote*≤ η ⇓ns) (quote≤ η ⇓n)
  quote*≤ η (prim⇓ ⇓nu ⇓nv ⇓ns) =
    prim⇓ (quote≤ η ⇓nu) (quote≤ η ⇓nv) (quote*≤ η ⇓ns)


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
