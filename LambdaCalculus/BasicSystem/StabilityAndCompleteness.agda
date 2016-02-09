module BasicSystem.StabilityAndCompleteness where

open import BasicSystem.Utils
open import BasicSystem.Syntax
open import BasicSystem.Conversion
open import BasicSystem.OPE
open import BasicSystem.OPELemmas
open import BasicSystem.BigStepSemantics
open import BasicSystem.StrongComputability
open import BasicSystem.StructuralNormaliser


--
-- Stability: nf (embNf n) ≡ n .
--

-- Nf embNf n ⇓ n

var≤∘suc : ∀ {α γ Β Γ} (η : Β ≤ γ ∷ Γ) (x : Var Γ α) →
  var≤ η (suc x) ≡ var≤ (η ● wk) x
var≤∘suc (≤weak η) x =
  cong suc (var≤∘suc η x)
var≤∘suc (≤lift η) x
  rewrite η ● ≤id ≡ η ∋ η●≤id η
  = refl

⟦embVar⟧≤⇓ : ∀ {α Β Γ} (η : Β ≤ Γ) (x : Var Γ α) →
  ⟦ embVar x ⟧ (env≤ η id-env) ⇓ ne (var (var≤ η x))
⟦embVar⟧≤⇓ η zero = ø⇓
⟦embVar⟧≤⇓ η (suc x)
  rewrite env≤ η (env≤ wk id-env) ≡ env≤ (η ● wk) id-env ∋ env≤∘ η wk id-env |
          var≤ η (suc x) ≡ var≤ (η ● wk) x ∋ var≤∘suc η x
  = []⇓ ↑⇓ (⟦embVar⟧≤⇓ (η ● wk) x)

⟦embVar⟧⇓ : ∀ {α Γ} (x : Var Γ α) →
  ⟦ embVar x ⟧ id-env ⇓ ne (var x)
⟦embVar⟧⇓ {α} {Γ} x
  with ⟦embVar⟧≤⇓ ≤id x
... | r
  rewrite env≤ ≤id id-env ≡ id-env ∋ env≤-≤id {Γ} {Γ} id-env |
          var≤ ≤id x ≡ x ∋ var≤-≤id x
  = r

mutual

  stable⇓ : ∀ {α Γ} (n : Nf Γ α) → Nf embNf n ⇓ n
  stable⇓ (ne ns)
    with stable*⇓ ns
  ... | us , ⇓us , ⇓ns
    = nf⇓ ⇓us (⋆⇓ us ⇓ns)
  stable⇓ (lam n)
    with stable⇓ n
  ... | nf⇓ ⇓u ⇓n
    = nf⇓ ƛ⇓ (⇒⇓ (lam⇓ ⇓u) ⇓n)

  stable*⇓ : ∀ {α Γ} (ns : NeNf Γ α) →
    ∃ λ (us : NeVal Γ α) →
      ⟦ embNeNf ns ⟧ id-env ⇓ ne us × Quote* us ⇓ ns
  stable*⇓ (var x) =
    var x , ⟦embVar⟧⇓ x , var⇓
  stable*⇓ (app ns n) with stable*⇓ ns | stable⇓ n
  ... | us , ⇓us , ⇓ns | nf⇓ {u = u} ⇓u ⇓n =
    app us u , ∙⇓ ⇓us ⇓u ne⇓ , app⇓ ⇓ns ⇓n


-- nf (embNf n) ≡ n

stable : ∀ {α Γ} (n : Nf Γ α) → nf (embNf n) ≡ n
stable n =
  nf⇓→nf (embNf n) (stable⇓ n)


--
-- Completeness: terms are convertible to their normal forms.
--

complete : ∀ {α Γ} (t : Tm Γ α) → t ≈ embNf (nf t)

complete t
  with all-scv t id-env sce-id-env
... | u , p , ⇓u , ≈u
  with all-quote u p
... | n , ⇓n , ≈n
  with nf t & nf⇓ ⇓u ⇓n
... | n′ , n′≡n rewrite n′≡n
  = begin
  t
    ≈⟨ ≈sym ≈id ⟩
  t [ ı ]
    ≈⟨ ≈cong[] ≈refl (≈≈sym embEnv∘id-env) ⟩
  t [ embEnv id-env ]
    ≈⟨ ≈u ⟩
  embVal u
    ≈⟨ ≈n ⟩
  embNf n
  ∎
  where open ≈-Reasoning
