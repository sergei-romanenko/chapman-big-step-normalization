module BasicSystem.OPELemmas where

open import BasicSystem.Utils
open import BasicSystem.Syntax
open import BasicSystem.Conversion
open import BasicSystem.OPE


--
-- Composing OPEs.
--

η●≤id : ∀ {Γ Δ} (η : Γ ≤ Δ) → η ● ≤id ≡ η
η●≤id ≤[]     = refl 
η●≤id (≤lift η) = cong ≤lift (η●≤id η) 
η●≤id (≤weak η) = cong ≤weak (η●≤id η)

≤id●η : ∀ {Γ Δ} (η : Γ ≤ Δ) → ≤id ● η ≡ η
≤id●η ≤[]       = refl 
≤id●η (≤lift η) = cong ≤lift (≤id●η η) 
≤id●η (≤weak η) = cong ≤weak (≤id●η η)

assoc● :  ∀ {Β Γ₁ Γ₂ Δ} (η : Β ≤ Γ₁) (η′ : Γ₁ ≤ Γ₂) (η′′ : Γ₂ ≤ Δ) →
  (η ● η′) ● η′′ ≡ η ● (η′ ● η′′)
assoc● ≤[] ≤[] ≤[] = refl
assoc● (≤weak η) η′ η′′ = cong ≤weak (assoc● η η′ η′′)
assoc● (≤lift η) (≤weak η′) η′′ = cong ≤weak (assoc● η η′ η′′)
assoc● (≤lift η) (≤lift η′) (≤weak η′′) = cong ≤weak (assoc● η η′ η′′)
assoc● (≤lift η) (≤lift η′) (≤lift η′′) = cong ≤lift (assoc● η η′ η′′)


--
-- Applying ≤id.
--

var≤-≤id : ∀ {α Γ} (x : Var Γ α) → var≤ ≤id x ≡ x
var≤-≤id zero = refl
var≤-≤id (suc x) = cong suc (var≤-≤id x)

mutual

  val≤-≤id : ∀ {α Γ} (u : Val Γ α) → val≤ ≤id u ≡ u
  val≤-≤id (ne us) = cong ne (neVal≤-≤id us)
  val≤-≤id (lam t ρ) = cong (lam t) (env≤-≤id ρ)

  neVal≤-≤id : ∀ {α Γ} (us : NeVal Γ α) → neVal≤ ≤id us ≡ us
  neVal≤-≤id (var x) = cong var (var≤-≤id x)
  neVal≤-≤id (app us u) = cong₂ app (neVal≤-≤id us) (val≤-≤id u)

  env≤-≤id : ∀ {Γ Δ} (ρ : Env Δ Γ) → env≤ ≤id ρ ≡ ρ
  env≤-≤id [] = refl
  env≤-≤id (u ∷ ρ) = cong₂ _∷_ (val≤-≤id u) (env≤-≤id ρ)

--
-- Composing OPEs.
--

-- Variables.

var≤∘ : ∀ {α Γ₁ Γ₂ Γ₃}
  (η : Γ₁ ≤ Γ₂) (η′ : Γ₂ ≤ Γ₃) (x : Var Γ₃ α) →
  var≤ η (var≤ η′ x) ≡ var≤ (η ● η′) x
var≤∘ ≤[] ≤[] x = refl
var≤∘ (≤weak η) η′ x = cong suc (var≤∘ η η′ x)
var≤∘ (≤lift η) (≤weak η′) x = cong suc (var≤∘ η η′ x)
var≤∘ (≤lift η) (≤lift η′) zero = refl
var≤∘ (≤lift η) (≤lift η′) (suc x) = cong suc (var≤∘ η η′ x)

-- Values and environments.

mutual

  val≤∘ : ∀ {α Γ₁ Γ₂ Γ₃}
    (η : Γ₁ ≤ Γ₂) (η′ : Γ₂ ≤ Γ₃) (u : Val Γ₃ α) →
    val≤ η (val≤ η′ u) ≡ val≤ (η ● η′) u
  val≤∘ η η′ (ne us) = cong ne (neVal≤∘ η η′ us)
  val≤∘ η η′ (lam t ρ) = cong (lam t) (env≤∘ η η′ ρ)

  neVal≤∘ : ∀ {α Γ₁ Γ₂ Γ₃}
    (η : Γ₁ ≤ Γ₂) (η′ : Γ₂ ≤ Γ₃) (us : NeVal Γ₃ α) →
    neVal≤ η (neVal≤ η′ us) ≡ neVal≤ (η ● η′) us
  neVal≤∘ η η′ (var x) =
    cong var (var≤∘ η η′ x)
  neVal≤∘ η η′ (app us u) =
    cong₂ app (neVal≤∘ η η′ us) (val≤∘ η η′ u)

  env≤∘ : ∀ {α Γ₁ Γ₂ Γ₃}
    (η : Γ₁ ≤ Γ₂) (η′ : Γ₂ ≤ Γ₃) (ρ : Env Γ₃ α) →
    env≤ η (env≤ η′ ρ) ≡ env≤ (η ● η′) ρ
  env≤∘ η η′ [] = refl
  env≤∘ η η′ (u ∷ ρ) =
    cong₂ _∷_ (val≤∘ η η′ u) (env≤∘ η η′ ρ)


--
-- ≤2sub ≤id ≈≈ ı
--

ı≈≈≤2sub-≤id : ∀ {Γ} → ≤2sub {Γ} ≤id ≈≈ ı
ı≈≈≤2sub-≤id {[]} = ≈≈refl
ı≈≈≤2sub-≤id {α ∷ Γ} = begin
  ø ∷ ≤2sub ≤id ○ ↑
    ≈⟨ ≈≈cong∷ ≈refl (≈≈cong○ ı≈≈≤2sub-≤id ≈≈refl) ⟩
  ø ∷ ı ○ ↑
    ≈⟨ ≈≈sym ≈≈id∷ ⟩
  ı
  ∎
  where open ≈≈-Reasoning

--
-- OPEs commute with val≤ wk.
--

wk∘val≤ : ∀ {Β Γ α β} (η : Β ≤ Γ) (u : Val Γ α) →
  val≤ wk (val≤ η u) ≡ val≤ (≤lift {β} η) (val≤ wk u)
wk∘val≤ η u = begin
  val≤ wk (val≤ η u)
    ≡⟨⟩
  val≤ wk (val≤ η u)
    ≡⟨ val≤∘ wk η u ⟩
  val≤ (≤weak (≤id ● η)) u
    ≡⟨ cong (λ η′ → val≤ (≤weak η′) u) (≤id●η η) ⟩
  val≤ (≤weak η) u
    ≡⟨ cong (λ η′ → val≤ (≤weak η′) u) (sym $ η●≤id η) ⟩
  val≤ (≤weak (η ● ≤id)) u
    ≡⟨⟩
  val≤ (≤lift η ● wk) u
    ≡⟨ sym $ val≤∘ (≤lift η) wk u ⟩
  val≤ (≤lift η) (val≤ wk u)
    ≡⟨⟩
  val≤ (≤lift η) (val≤ wk u)
  ∎
  where open ≡-Reasoning


--
-- OPEs commute with embeddings.
--

-- Variables.

embVar∘≤ :  ∀ {α Β Γ} (η : Β ≤ Γ) (x : Var Γ α) →
  embVar (var≤ η x) ≈ embVar x [ ≤2sub η ]
embVar∘≤ ≤[] x = ≈sym ≈[ı]
embVar∘≤ (≤weak η) zero = begin
  embVar (var≤ (≤weak η) zero)
    ≡⟨⟩
  embVar (var≤ η zero) [ ↑ ]
    ≈⟨ ≈cong[] (embVar∘≤ η zero) ≈≈refl ⟩
  ø [ ≤2sub η ] [ ↑ ]
    ≈⟨ ≈sym ≈[○] ⟩
  ø [ ≤2sub η ○ ↑ ]
    ≡⟨⟩
  embVar zero [ ≤2sub (≤weak η) ]
  ∎
  where open ≈-Reasoning
embVar∘≤ (≤weak η) (suc x) = begin
  embVar (var≤ (≤weak η) (suc x))
    ≡⟨⟩
  embVar (var≤ η (suc x)) [ ↑ ]
    ≈⟨ ≈cong[] (embVar∘≤ η (suc x)) ≈≈refl ⟩
  embVar x [ ↑ ] [ ≤2sub η ] [ ↑ ]
    ≈⟨ ≈sym ≈[○] ⟩
  embVar x [ ↑ ] [ ≤2sub η ○ ↑ ]
    ≡⟨⟩
  embVar (suc x) [ ≤2sub (≤weak η) ]
  ∎
  where open ≈-Reasoning
embVar∘≤ (≤lift η) zero = begin
  embVar (var≤ (≤lift η) zero)
    ≡⟨⟩
  ø
    ≈⟨ ≈sym ≈ø[∷] ⟩
  ø [ ø ∷ ≤2sub η ○ ↑ ]
    ≡⟨⟩
  embVar zero [ ≤2sub (≤lift η) ]
  ∎
  where open ≈-Reasoning
embVar∘≤ (≤lift η) (suc x) = begin
  embVar (var≤ (≤lift η) (suc x))
    ≡⟨⟩
  embVar (var≤ η x) [ ↑ ]
    ≈⟨ ≈cong[] (embVar∘≤ η x) ≈≈refl ⟩
  embVar x [ ≤2sub η ] [ ↑ ]
    ≈⟨ ≈sym ≈[○] ⟩
  embVar x [ ≤2sub η ○ ↑ ]
    ≈⟨ ≈cong[] ≈refl (≈≈sym ≈≈wk) ⟩
  embVar x [ ↑ ○ (ø ∷ ≤2sub η ○ ↑) ]
    ≈⟨ ≈[○] ⟩
  embVar x [ ↑ ] [ ø ∷ ≤2sub η ○ ↑ ]
    ≡⟨⟩
  embVar (suc x) [ ≤2sub (≤lift η) ]
  ∎
  where open ≈-Reasoning

-- Values.

mutual

  embVal∘≤ : ∀ {α Β Γ} (η : Β ≤ Γ) (u : Val Γ α) →
    embVal (val≤ η u) ≈ embVal u [ ≤2sub η ]
  embVal∘≤ η (ne us) = embNeVal∘≤ η us
  embVal∘≤ η (lam t ρ) = begin
    embVal (val≤ η (lam t ρ))
      ≡⟨⟩
    (ƛ t) [ embEnv (env≤ η ρ) ]
      ≈⟨ ≈cong[] ≈refl (embEnv∘≤ η ρ) ⟩
    (ƛ t) [ embEnv ρ ○ ≤2sub η ]
      ≈⟨ ≈[○]  ⟩
    (ƛ t) [ embEnv ρ ] [ ≤2sub η ]
      ≡⟨⟩
    embVal (lam t ρ) [ ≤2sub η ]
    ∎
    where open ≈-Reasoning

  embNeVal∘≤ : ∀ {α Β Γ} (η : Β ≤ Γ) (us : NeVal Γ α) →
    embNeVal (neVal≤ η us) ≈ embNeVal us [ ≤2sub η ]
  embNeVal∘≤ η (var x) = embVar∘≤ η x
  embNeVal∘≤ η (app us u) = begin
    embNeVal (neVal≤ η (app us u))
      ≡⟨⟩
    embNeVal (neVal≤ η us) ∙ embVal (val≤ η u)
      ≈⟨ ≈cong∙ (embNeVal∘≤ η us) (embVal∘≤ η u) ⟩
    embNeVal us [ ≤2sub η ] ∙ embVal u [ ≤2sub η ]
      ≈⟨ ≈sym ≈∙[] ⟩
    (embNeVal us ∙ embVal u) [ ≤2sub η ]
      ≡⟨⟩
    embNeVal (app us u) [ ≤2sub η ]
    ∎
    where open ≈-Reasoning

  embEnv∘≤ : ∀ {Β Γ Δ} (η : Β ≤ Γ) (ρ : Env Γ Δ) →
    embEnv (env≤ η ρ) ≈≈ embEnv ρ ○ ≤2sub η
  embEnv∘≤ ≤[] [] = ≈≈sym ≈≈idr
  embEnv∘≤ {Γ = []} (≤weak η) [] = begin
    embEnv (env≤ (≤weak η) [])
      ≡⟨⟩
    sub-from-[] ○ ↑
      ≈⟨ ≈≈cong○ (embEnv∘≤ η []) ≈≈refl ⟩
    (ı ○ ≤2sub η) ○ ↑
      ≈⟨ ≈≈assoc ⟩
    ı ○ ≤2sub η ○ ↑
      ≡⟨⟩
    embEnv [] ○ ≤2sub (≤weak η)
    ∎
    where open ≈≈-Reasoning
  embEnv∘≤ {Γ = α ∷ Γ} (≤weak η) [] = begin
    embEnv (env≤ (≤weak η) [])
      ≡⟨⟩
    sub-from-[] ○ ↑
      ≈⟨ ≈≈cong○ (embEnv∘≤ η []) ≈≈refl ⟩
    ((sub-from-[] ○ ↑) ○ ≤2sub η) ○ ↑
      ≈⟨ ≈≈assoc ⟩
    (sub-from-[] ○ ↑) ○ (≤2sub η ○ ↑)
      ≡⟨⟩
    embEnv [] ○ ≤2sub (≤weak η)
    ∎
    where open ≈≈-Reasoning
  embEnv∘≤ (≤lift η) [] = begin
    embEnv (env≤ (≤lift η) [])
      ≡⟨⟩
    sub-from-[] ○ ↑
      ≈⟨ ≈≈cong○ (embEnv∘≤ η []) ≈≈refl ⟩
    (sub-from-[] ○ ≤2sub η) ○ ↑
      ≈⟨ ≈≈assoc ⟩
    sub-from-[] ○ (≤2sub η ○ ↑)
      ≈⟨ ≈≈cong○ ≈≈refl (≈≈sym ≈≈wk) ⟩
    sub-from-[] ○ (↑ ○ (ø ∷ ≤2sub η ○ ↑))
      ≈⟨ ≈≈sym ≈≈assoc ⟩
    (sub-from-[] ○ ↑) ○ (ø ∷ ≤2sub η ○ ↑)
      ≡⟨⟩
    embEnv [] ○ ≤2sub (≤lift η)
    ∎
    where open ≈≈-Reasoning
  embEnv∘≤ η (u ∷ ρ) = begin
    embEnv (env≤ η (u ∷ ρ))
      ≡⟨⟩
    embVal (val≤ η u) ∷ embEnv (env≤ η ρ)
      ≈⟨ ≈≈cong∷ (embVal∘≤ η u) (embEnv∘≤ η ρ) ⟩
    embVal u [ ≤2sub η ] ∷ embEnv ρ ○ ≤2sub η
      ≈⟨ ≈≈sym ≈≈cons ⟩
    (embVal u ∷ embEnv ρ) ○ ≤2sub η
      ≡⟨⟩
    embEnv (u ∷ ρ) ○ ≤2sub η
    ∎
    where open ≈≈-Reasoning

-- Normal forms.

mutual

  embNf∘≤ : ∀ {α Β Γ} (η : Β ≤ Γ) (n : Nf Γ α) →
    embNf (nf≤ η n) ≈ embNf n [ ≤2sub η ]
  embNf∘≤ η (ne⋆ ns) = embNeNf∘≤ η ns
  embNf∘≤ η (lam n) = begin
    embNf (nf≤ η (lam n))
      ≡⟨⟩
    ƛ embNf (nf≤ (≤lift η) n)
      ≈⟨ ≈congƛ (embNf∘≤ (≤lift η) n) ⟩
    ƛ embNf n [ ø ∷ ≤2sub η ○ ↑ ]
      ≈⟨ ≈sym ≈ƛ[] ⟩
    (ƛ embNf n) [ ≤2sub η ]
      ≡⟨⟩
    embNf (lam n) [ ≤2sub η ]
    ∎
    where open ≈-Reasoning

  embNeNf∘≤ : ∀ {α Β Γ} (η : Β ≤ Γ) (ns : NeNf Γ α) →
    embNeNf (neNf≤ η ns) ≈ embNeNf ns [ ≤2sub η ]
  embNeNf∘≤ η (var x) = embVar∘≤ η x
  embNeNf∘≤ η (app ns u) = begin
    embNeNf (neNf≤ η (app ns u))
      ≡⟨⟩
    embNeNf (neNf≤ η ns) ∙ embNf (nf≤ η u)
      ≈⟨ ≈cong∙ (embNeNf∘≤ η ns) (embNf∘≤ η u) ⟩
    (embNeNf ns [ ≤2sub η ]) ∙ (embNf u [ ≤2sub η ])
      ≈⟨ ≈sym ≈∙[] ⟩
    (embNeNf ns ∙ embNf u) [ ≤2sub η ]
      ≡⟨⟩
    embNeNf (app ns u) [ ≤2sub η ]
    ∎
    where open ≈-Reasoning

--
-- embEnv id-env ≈≈ ı
--

embEnv∘id-env : ∀ {Γ} → embEnv (id-env {Γ}) ≈≈ ı
embEnv∘id-env {[]} = ≈≈refl
embEnv∘id-env {γ ∷ Γ} = begin
  ø ∷ embEnv (env≤ wk id-env)
    ≡⟨⟩
  ø ∷ embEnv (env≤ wk id-env)
    ≈⟨ ≈≈cong∷ ≈refl (embEnv∘≤ wk id-env) ⟩
  ø ∷ embEnv id-env ○ (≤2sub ≤id ○ ↑)
    ≈⟨ ≈≈cong∷ ≈refl (≈≈cong○ ≈≈refl (≈≈cong○ ı≈≈≤2sub-≤id ≈≈refl)) ⟩
  ø ∷ embEnv id-env ○ (ı ○ ↑)
    ≈⟨ ≈≈cong∷ ≈refl (≈≈cong○ embEnv∘id-env ≈≈idl) ⟩
  ø ∷ (ı ○ ↑)
    ≈⟨ ≈≈sym ≈≈id∷ ⟩
  ı
  ∎
  where open ≈≈-Reasoning
