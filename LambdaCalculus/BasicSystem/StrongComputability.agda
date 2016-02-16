module BasicSystem.StrongComputability where

open import BasicSystem.Utils
open import BasicSystem.Syntax
open import BasicSystem.Conversion
open import BasicSystem.OPE
open import BasicSystem.OPELemmas
open import BasicSystem.BigStepSemantics
open import BasicSystem.OPEBigStep


--
-- Strong computability.
--

SCV : ∀ {α Γ} (u : Val Γ α) → Set
SCV {⋆} {Γ} (ne us) = ∃ λ (ns : NeNf Γ ⋆) →
  Quote* us ⇓ ns
  × embNeVal us ≈ embNeNf ns
SCV {α ⇒ β} {Γ} u = ∀ {Β} (η : Β ≤ Γ) (v : Val Β α) (q : SCV v) →
  ∃ λ w → SCV w
    × (val≤ η u) ⟨∙⟩ v ⇓ w
    × embVal (val≤ η u) ∙ embVal v ≈ embVal w

infixr 5 _∷_

data SCE {Γ : Ctx} : ∀ {Δ : Ctx} (ρ : Env Γ Δ) → Set where
  [] : SCE []
  _∷_ : ∀ {α Δ} {u : Val Γ α} (p : SCV u) {ρ : Env Γ Δ} (q : SCE ρ) →
    SCE (u ∷ ρ)

--
-- Weakening for SCV & SCE.
--
-- (η : Β ≤ Γ) (p : SCV u) → SCV (val≤ η u)
-- (η : Β ≤ Γ) (r : SCE ρ) → SCE (env≤ η ρ)
--

mutual

  scv≤ :  ∀ {α Γ Β} (η : Β ≤ Γ) (u : Val Γ α) (p : SCV u) →
    SCV (val≤ η u)
  scv≤ {⋆}  η (ne us) (ns , p , q) =
    neNf≤ η ns , quote*≤ η p , embNe≤≈ η us ns q
  scv≤ {α ⇒ β} η u p {Β′} η′ v q
    with p (η′ ● η) v q
  ... | w , r , ●⇓w , ●≈w
    rewrite val≤ η′ (val≤ η u) ≡ val≤ (η′ ● η) u ∋ val≤∘ η′ η u
    = w , r , ●⇓w , ●≈w

  sce≤ : ∀ {Γ Δ Β} (η : Β ≤ Γ) (ρ : Env Γ Δ) (r : SCE ρ) →
    SCE (env≤ η ρ)
  sce≤ η [] [] = []
  sce≤ η (u ∷ ρ) (p ∷ r) = scv≤ η u p ∷ sce≤ η ρ r

--
-- embVal (val≤ wk u) ≈ embVal u [ ↑ ]
--

embVal∘wk : ∀ {α γ Γ} (u : Val Γ α) →
  embVal (val≤ wk {α} u) ≈ embVal u [ ↑ {γ} ]
embVal∘wk u = begin
  embVal (val≤ wk u)
    ≡⟨⟩
  embVal (val≤ wk u)
    ≈⟨ embVal∘≤ wk u ⟩
  embVal u [ ≤2sub ≤id ○ ↑ ]
    ≈⟨ ≈cong[] ≈refl (≈≈cong○ ı≈≈≤2sub-≤id ≈≈refl) ⟩
  embVal u [ ı ○ ↑ ]
    ≈⟨ ≈cong[] ≈refl ≈≈idl ⟩
  embVal u [ ↑ ]
  ∎
  where open ≈-Reasoning


--
-- ∃ λ n → Quote u ⇓ n × embVal u ≈ embNf n
-- Quote* us ⇓ ns → embNeVal us ≈ embNeNf ns → SCV (ne us)
--

mutual

  all-quote : ∀ {α Γ} (u : Val Γ α) (p : SCV u) →
    ∃ λ n → Quote u ⇓ n × embVal u ≈ embNf n
  all-quote {⋆} (ne us) (ns , ⇓ns , ≈ns) =
    ne⋆ ns , ⋆⇓ us ⇓ns , ≈ns
  all-quote {α ⇒ β} {Γ} u p
    with all-scv-ne {α} {α ∷ Γ} (var zero) (var zero) var⇓ ≈refl
  ... | r with p wk (ne (var zero)) r
  ... | v , q , ⇓v , ≈v with all-quote {β} v q
  ... | m , ⇓m , ≈m
    = lam m , ⇒⇓ ⇓v ⇓m ,
      (begin
        embVal u
          ≈⟨ ≈η ⟩
        ƛ embVal u [ ↑ ] ∙ ø
          ≈⟨ ≈congƛ (≈cong∙ (≈sym (embVal∘wk u)) ≈refl) ⟩
        ƛ embVal (val≤ wk u) ∙ ø
          ≈⟨ ≈congƛ ≈v ⟩
        ƛ embVal v
          ≈⟨ ≈congƛ ≈m ⟩
        ƛ embNf m
          ≡⟨⟩
        embNf (lam m)
      ∎)
    where open ≈-Reasoning
         
  all-scv-ne : ∀ {α Γ} (us : NeVal Γ α) (ns : NeNf Γ α) →
    Quote* us ⇓ ns → embNeVal us ≈ embNeNf ns → SCV (ne us)
  all-scv-ne {⋆} us ns ⇓ns ≈ns =
    ns , ⇓ns , ≈ns
  all-scv-ne {α ⇒ β} {Γ} us ns ⇓ns ≈ns {Β} η u p
    with all-quote u p
  ... | n , ⇓n , ≈n
    = ne (app us≤ u) , r , ne⇓ , ≈refl
    where
    open ≈-Reasoning
    us≤ = neVal≤ η us
    ns≤ = neNf≤ η ns
    ⇓ns≤ = quote*≤ η ⇓ns

    us∙u≈ns∙n = begin
      embNeVal us≤ ∙ embVal u
        ≈⟨ ≈cong∙ (embNe≤≈ η us ns ≈ns) ≈n ⟩
      embNeNf ns≤ ∙ embNf n ∎

    r : SCV (ne (app us≤ u))
    r = all-scv-ne (app us≤ u) (app ns≤ n) (app⇓ ⇓ns≤ ⇓n) us∙u≈ns∙n


-- SCE id-env

scv-var : ∀ {α Γ} (x : Var Γ α) → SCV (ne (var x))
scv-var x = all-scv-ne (var x) (var x) var⇓ ≈refl

sce-id-env : ∀ {Γ} → SCE (id-env {Γ})
sce-id-env {[]} = []
sce-id-env {γ ∷ Γ} =
  scv-var zero ∷ sce≤ wk id-env sce-id-env

--
-- The fundamental theorem about strong computability:
-- all terms are "strongly computable".
--   ∃ λ u → SCV u × ⟦ t ⟧ ρ ⇓ u × (t [ embEnv ρ ] ≈ embVal u)
--   ∃ λ θ → SCE θ × ⟦ σ ⟧* ρ ⇓ θ × (σ ○ embEnv ρ ≈≈ embEnv θ)
--

mutual

  all-scv : ∀ {α Γ Δ} (t : Tm Δ α) (ρ : Env Γ Δ) (r : SCE ρ) →
    ∃ λ u → SCV u × ⟦ t ⟧ ρ ⇓ u × (t [ embEnv ρ ] ≈ embVal u)

  all-scv ø (u ∷ ρ) (p ∷ r) =
    u , p , ø⇓ , ≈proj
  all-scv {β} {Γ} {Δ} (t ∙ t′) ρ r with all-scv t ρ r | all-scv t′ ρ r
  ... | u , p , ⇓u , ≈u | v , q , ⇓v , ≈v
    with p ≤id v q
  ... | w , cw , ⇓w , ≈w
    rewrite val≤-≤id u
    = w , cw , ∙⇓ ⇓u ⇓v ⇓w ,
      (begin
        (t ∙ t′) [ embEnv ρ ]
          ≈⟨ ≈app ⟩
        t [ embEnv ρ ] ∙ t′ [ embEnv ρ ]
          ≈⟨ ≈cong∙ ≈u ≈v ⟩
        embVal u ∙ embVal v
          ≈⟨ ≈w ⟩
        embVal w
      ∎)
    where open ≈-Reasoning
  all-scv (ƛ t) ρ r =
    lam t ρ , h , ƛ⇓ , ≈refl
    where
    open ≈-Reasoning
    h : SCV (lam t ρ)
    h η u p
      with all-scv t (u ∷ env≤ η ρ) (p ∷ sce≤ η ρ r)
    ... | v , q , ∷⇓v , ≈v
      = v , q , lam⇓ ∷⇓v ,
        (begin
          (ƛ t) [ embEnv (env≤ η ρ) ] ∙ embVal u
            ≈⟨ ≈βσ ⟩
          t [ embVal u ∷ embEnv (env≤ η ρ) ]
            ≈⟨ ≈v ⟩
          embVal v
        ∎)
  all-scv (t [ σ ]) ρ r
    with all-sce σ ρ r
  ... | θ , cθ , ⇓θ , ≈≈θ
    with all-scv t θ cθ
  ... | u , p , ⇓u , ≈u
    = u , p , []⇓ ⇓θ ⇓u ,
      (begin
        t [ σ ] [ embEnv ρ ]
          ≈⟨ ≈sym ≈comp ⟩
        t [ σ ○ embEnv ρ ]
          ≈⟨ ≈cong[] ≈refl ≈≈θ ⟩
        t [ embEnv θ ]
          ≈⟨ ≈u ⟩
        embVal u
      ∎)
    where open ≈-Reasoning

  all-sce : ∀ {Β Γ Δ} (σ : Sub Γ Δ) (ρ : Env Β Γ) (r : SCE ρ) →
    ∃ λ θ → SCE θ × ⟦ σ ⟧* ρ ⇓ θ × (σ ○ embEnv ρ ≈≈ embEnv θ)

  all-sce ı ρ r =
    ρ , r , ι⇓ , ≈≈idl
  all-sce (σ ○ σ′) ρ r
    with all-sce σ′ ρ r
  ... | θ′ , r′ , ⇓θ′ , ≈≈θ′
    with all-sce σ θ′ r′
  ... | θ′′ , r′′ , ⇓θ′′ , ≈≈θ′′
    = θ′′ , r′′ , ○⇓ ⇓θ′ ⇓θ′′ ,
      (begin
        (σ ○ σ′) ○ embEnv ρ
          ≈⟨ ≈≈assoc ⟩
        σ ○ (σ′ ○ embEnv ρ)
          ≈⟨ ≈≈cong○ ≈≈refl ≈≈θ′ ⟩
        σ ○ embEnv θ′
          ≈⟨ ≈≈θ′′ ⟩
        embEnv θ′′
      ∎)
    where open ≈≈-Reasoning
  all-sce (t ∷ σ) ρ r
    with all-scv t ρ r | all-sce σ ρ r
  ... | u , p , ⇓u , ≈u | θ′ , r′ , ⇓θ′ , ≈≈θ′
    = u ∷ θ′ , (p ∷ r′) , ∷⇓ ⇓u ⇓θ′ ,
      (begin
        (t ∷ σ) ○ embEnv ρ
          ≈⟨ ≈≈cons ⟩
        t [ embEnv ρ ] ∷ (σ ○ embEnv ρ)
          ≈⟨ ≈≈cong∷ ≈u ≈≈refl ⟩
        embVal u ∷ (σ ○ embEnv ρ)
          ≈⟨ ≈≈cong∷ ≈refl ≈≈θ′ ⟩
        embVal u ∷ embEnv θ′
      ∎)
    where open ≈≈-Reasoning
  all-sce ↑ (u ∷ ρ) (p ∷ r) =
    ρ , r , ↑⇓ , ≈≈wk
