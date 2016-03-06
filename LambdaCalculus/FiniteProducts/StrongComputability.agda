module FiniteProducts.StrongComputability where

open import FiniteProducts.Utils
open import FiniteProducts.Syntax
open import FiniteProducts.Conversion
open import FiniteProducts.OPE
open import FiniteProducts.OPELemmas
open import FiniteProducts.BigStepSemantics
open import FiniteProducts.OPEBigStep


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
SCV {One} u = ⊤
SCV {α * β} {Γ} u =
  (∃ λ w → SCV w × Fst u ⇓ w × fst (embVal u) ≈ embVal w) ×
  (∃ λ w → SCV w × Snd u ⇓ w × snd (embVal u) ≈ embVal w)

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
  scv≤ {α ⇒ β} {Γ} {Β} η u p {Β′} η′ v q
    with p (η′ ● η) v q
  ... | w , r , ●⇓w , ●≈w =
    w , r , ∘⇓w , ∘≈w≤
    where
    open ≈-Reasoning
    ∘≡● : val≤ η′ (val≤ η u) ≡ val≤ (η′ ● η) u
    ∘≡● = val≤∘ η′ η u
    ∘⇓w : val≤ η′ (val≤ η u) ⟨∙⟩ v ⇓ w
    ∘⇓w = subst (λ f → f ⟨∙⟩ v ⇓ w) (sym $ ∘≡●) ●⇓w
    ∘≈w≤ : embVal (val≤ η′ (val≤ η u)) ∙ embVal v ≈ embVal w
    ∘≈w≤ = begin
      embVal (val≤ η′ (val≤ η u)) ∙ embVal v
        ≡⟨ cong₂ _∙_ (cong embVal (val≤∘ η′ η u)) refl ⟩
      embVal (val≤ (η′ ● η) u) ∙ embVal v
        ≈⟨ ●≈w ⟩
      embVal w
      ∎
  scv≤ {One} η u tt = tt
  scv≤ {α * β} η u ((w₁ , p₁ , ⇓w₁ , ≈w₁) , (w₂ , p₂ , ⇓w₂ , ≈w₂)) =
    (val≤ η w₁ , scv≤ η w₁ p₁ , fst⇓≤ η ⇓w₁ , fst∘embVal≈ (fst⇓≤ η ⇓w₁)) ,
    (val≤ η w₂ , scv≤ η w₂ p₂ , snd⇓≤ η ⇓w₂ , snd∘embVal≈ (snd⇓≤ η ⇓w₂))

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
  ... | r
    with p wk (ne (var zero)) r
  ... | v , q , ⇓v , ≈v
    with all-quote {β} v q
  ... | m , ⇓m , ≈m =
    lam m , ⇒⇓ ⇓v ⇓m , u≈m
    where
    open ≈-Reasoning
    u≈m : embVal u ≈ embNf (lam m)
    u≈m = begin
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
      ∎
  all-quote {One} {Γ} u tt =
    void , One⇓ , ≈ηvoid
  all-quote {α * β} {Γ} uv ((u , p , ⇓u , ≈u) , (v , q , ⇓v , ≈v))
    with all-quote u p | all-quote v q
  ... | nu , ⇓nu , ≈nu | nv , ⇓nv , ≈nv
    = pair nu nv , Prod⇓ ⇓u ⇓nu ⇓v ⇓nv , uv≈pair
    where
    open ≈-Reasoning
    uv≈pair : embVal uv ≈ pair (embNf nu) (embNf nv)
    uv≈pair = begin
      embVal uv
        ≈⟨ ≈ηpair ⟩
      pair (fst (embVal uv)) (snd (embVal uv))
        ≈⟨ ≈cong-pair ≈u ≈v ⟩
      pair (embVal u) (embVal v)
        ≈⟨ ≈cong-pair ≈nu ≈nv ⟩
      pair (embNf nu) (embNf nv)
      ∎
        
  all-scv-ne : ∀ {α Γ} (us : NeVal Γ α) (ns : NeNf Γ α) →
    Quote* us ⇓ ns → embNeVal us ≈ embNeNf ns → SCV (ne us)
  all-scv-ne {⋆} us ns ⇓ns ≈ns =
    ns , ⇓ns , ≈ns
  all-scv-ne {α ⇒ β} {Γ} us ns ⇓ns ≈ns {Β} η u p
    with all-quote u p
  ... | n , ⇓n , ≈n =
    ne (app us≤ u) , r , ne⇓ , ≈refl
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
    r = all-scv-ne (app us≤ u) (app ns≤ n)
                        (app⇓ ⇓ns≤ ⇓n) us∙u≈ns∙n
  all-scv-ne {One} us ns ⇓ns ≈ns = tt
  all-scv-ne {α * β} {Γ} us ns ⇓ns ≈ns =
    (ne (fst us) ,
      all-scv-ne (fst us) (fst ns) (fst⇓ ⇓ns) (≈cong-fst ≈ns) ,
      fst-ne⇓ , ≈refl) ,
    (ne (snd us) ,
      all-scv-ne (snd us) (snd ns) (snd⇓ ⇓ns) (≈cong-snd ≈ns) ,
      snd-ne⇓ , ≈refl)


-- SCE id-env

scv-var : ∀ {α Γ} (x : Var Γ α) → SCV (ne (var x))
scv-var x = all-scv-ne (var x) (var x) var⇓ ≈refl

sce-id-env : ∀ {Γ} → SCE (id-env {Γ})
sce-id-env {[]} = []
sce-id-env {γ ∷ Γ} =
  scv-var {γ} zero ∷ sce≤ wk id-env sce-id-env

--
-- The fundamental theorem about strong computability:
-- all terms are "strongly computable".
--

mutual

  all-scv : ∀ {α Γ Δ} (t : Tm Δ α) (ρ : Env Γ Δ) (r : SCE ρ) →
    ∃ λ u → SCV u × ⟦ t ⟧ ρ ⇓ u × (t [ embEnv ρ ] ≈ embVal u)

  all-scv ø (u ∷ ρ) (p ∷ r) =
    u , p , ø⇓ , ≈ø[∷]
  all-scv {β} {Γ} {Δ} (f ∙ a) ρ r with all-scv f ρ r | all-scv a ρ r
  ... | u , p , ⇓u , ≈u | v , q , ⇓v , ≈v with p ≤id v q
  ... | w , r′ , ⇓w , ≈w =
    w , r′ , ∙⇓ ⇓u ⇓v ⇓w′ , ≈w′
    where
    open ≈-Reasoning
    ⇓w′ : u ⟨∙⟩ v ⇓ w
    ⇓w′ = subst (λ u′ → u′ ⟨∙⟩ v ⇓ w) (val≤-≤id u) ⇓w
    ≈w′ : (f ∙ a) [ embEnv ρ ] ≈ embVal w
    ≈w′ = begin
      (f ∙ a) [ embEnv ρ ]
        ≈⟨ ≈∙[] ⟩
      f [ embEnv ρ ] ∙ a [ embEnv ρ ]
        ≈⟨ ≈cong∙ ≈u ≈v ⟩
      embVal u ∙ embVal v
        ≡⟨ cong₂ _∙_ (cong embVal (sym $ val≤-≤id u)) refl ⟩
      embVal (val≤ ≤id u) ∙ embVal v
        ≈⟨ ≈w ⟩
      embVal w
      ∎
  all-scv (ƛ t) ρ r =
    lam t ρ , r′ , ƛ⇓ , ≈refl
    where
    r′ : SCV (lam t ρ)
    r′ η u p with all-scv t (u ∷ env≤ η ρ) (p ∷ sce≤ η ρ r)
    ... | v , q , ∷⇓v , ≈v =
      v , q , lam⇓ ∷⇓v , ≈v′
      where
      open ≈-Reasoning
      ≈v′ : (ƛ t) [ embEnv (env≤ η ρ) ] ∙ embVal u ≈ embVal v
      ≈v′ = begin
        (ƛ t) [ embEnv (env≤ η ρ) ] ∙ embVal u
          ≈⟨ ≈βσ ⟩
        t [ embVal u ∷ embEnv (env≤ η ρ) ]
          ≈⟨ ≈v ⟩
        embVal v
        ∎
  all-scv (t [ σ ]) ρ r
    with all-sce σ ρ r
  ... | θ′ , r′ , ⇓θ′ , ≈≈θ′
    with all-scv t θ′ r′
  ... | u , p , ⇓u , ≈u =
    u , p , ⇓u′ , ≈u′
    where
    open ≈-Reasoning
    ⇓u′ : ⟦ t [ σ ] ⟧ ρ ⇓ u
    ⇓u′ = []⇓ ⇓θ′ ⇓u
    ≈u′ : t [ σ ] [ embEnv ρ ] ≈ embVal u
    ≈u′ = begin
      t [ σ ] [ embEnv ρ ]
        ≈⟨ ≈sym ≈[○] ⟩
      t [ σ ○ embEnv ρ ]
        ≈⟨ ≈cong[] ≈refl ≈≈θ′ ⟩
      t [ embEnv θ′ ]
        ≈⟨ ≈u ⟩
      embVal u
      ∎
  all-scv void ρ r =
    void , tt , void⇓ , ≈void[]
  all-scv (pair ta tb) ρ r
    with all-scv ta ρ r | all-scv tb ρ r
  ... | u , p , ⇓u , ≈u | v , q , ⇓v , ≈v
    =
    pair u v , ((u , p , fst-pair⇓ , ≈βfst) , (v , q , snd-pair⇓ , ≈βsnd)) ,
      pair⇓ ⇓u ⇓v , pair[]≈
    where
    open ≈-Reasoning
    pair[]≈ : pair ta tb [ embEnv ρ ] ≈ pair (embVal u) (embVal v)
    pair[]≈ = begin
      pair ta tb [ embEnv ρ ]
        ≈⟨ ≈pair[] ⟩
      pair (ta [ embEnv ρ ]) (tb [ embEnv ρ ])
        ≈⟨ ≈cong-pair ≈u ≈v ⟩
      pair (embVal u) (embVal v)
      ∎
  all-scv (fst t) ρ r
    with all-scv t ρ r
  ... | uv , ((u , p , ⇓u , ≈u) , (v , q , ⇓v , ≈v)) , ⇓uv , ≈uv
    = u , p , fst⇓ ⇓uv ⇓u , fst[]≈
    where
    open ≈-Reasoning
    fst[]≈ : fst t [ embEnv ρ ] ≈ embVal u
    fst[]≈ = begin
      fst t [ embEnv ρ ]
        ≈⟨ ≈fst[] ⟩
      fst (t [ embEnv ρ ])
        ≈⟨ ≈cong-fst ≈uv ⟩
      fst (embVal uv)
        ≈⟨ ≈u ⟩
      embVal u
      ∎
  all-scv (snd t) ρ r
    with all-scv t ρ r
  ... | uv , ((u , p , ⇓u , ≈u) , (v , q , ⇓v , ≈v)) , ⇓uv , ≈uv
    = v , q , snd⇓ ⇓uv ⇓v , snd[]≈
    where
    open ≈-Reasoning
    snd[]≈ : snd t [ embEnv ρ ] ≈ embVal v
    snd[]≈ = begin
      snd t [ embEnv ρ ]
        ≈⟨ ≈snd[] ⟩
      snd (t [ embEnv ρ ])
        ≈⟨ ≈cong-snd ≈uv ⟩
      snd (embVal uv)
        ≈⟨ ≈v ⟩
      embVal v
      ∎

  all-sce : ∀ {Β Γ Δ} (σ : Sub Γ Δ) (ρ : Env Β Γ) (r : SCE ρ) →
    ∃ λ θ → SCE θ × ⟦ σ ⟧* ρ ⇓ θ × (σ ○ embEnv ρ ≈≈ embEnv θ)

  all-sce ı ρ r =
    ρ , r , ι⇓ , ≈≈idl
  all-sce (σ ○ τ) ρ r
    with all-sce τ ρ r
  ... | θ′ , r′ , ⇓θ′ , ≈≈θ′
    with all-sce σ θ′ r′
  ... | θ′′ , r′′ , ⇓θ′′ , ≈≈θ′′ =
    θ′′ , r′′ , ○⇓ ⇓θ′ ⇓θ′′ , ≈≈θ′′′
    where
    open ≈≈-Reasoning
    ≈≈θ′′′ : (σ ○ τ) ○ embEnv ρ ≈≈ embEnv θ′′
    ≈≈θ′′′ = begin
      (σ ○ τ) ○ embEnv ρ
        ≈⟨ ≈≈assoc ⟩
      σ ○ (τ ○ embEnv ρ)
        ≈⟨ ≈≈cong○ ≈≈refl ≈≈θ′ ⟩
      σ ○ embEnv θ′
        ≈⟨ ≈≈θ′′ ⟩
      embEnv θ′′
      ∎
  all-sce (t ∷ σ) ρ r
    with all-scv t ρ r | all-sce σ ρ r
  ... | u , p , ⇓u , ≈u | θ′ , r′ , ⇓θ′ , ≈≈θ′ =
    u ∷ θ′ , (p ∷ r′) , ∷⇓ ⇓u ⇓θ′ , ≈≈u∷θ′
    where
    open ≈≈-Reasoning
    ≈≈u∷θ′ : (t ∷ σ) ○ embEnv ρ ≈≈ embVal u ∷ embEnv θ′
    ≈≈u∷θ′ = begin
      (t ∷ σ) ○ embEnv ρ
        ≈⟨ ≈≈cons ⟩
      t [ embEnv ρ ] ∷ (σ ○ embEnv ρ)
        ≈⟨ ≈≈cong∷ ≈u ≈≈refl ⟩
      embVal u ∷ (σ ○ embEnv ρ)
        ≈⟨ ≈≈cong∷ ≈refl ≈≈θ′ ⟩
      embVal u ∷ embEnv θ′
      ∎
  all-sce ↑ (u ∷ ρ) (p ∷ r) =
    ρ , r , ↑⇓ , ≈≈wk
