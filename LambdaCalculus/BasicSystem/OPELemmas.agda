module BasicSystem.OPELemmas where

open import BasicSystem.Syntax
open import BasicSystem.OPE
open import BasicSystem.Utils
open import BasicSystem.Embeddings
open import BasicSystem.Conversion

rightid : ∀ {Γ Δ} (f : OPE Γ Δ) → comp f oid ≡ f
rightid done     = refl 
rightid (keep σ f) = cong (keep σ) (rightid f) 
rightid (skip σ f) = cong (skip σ) (rightid f)

leftid : ∀ {Γ Δ} (f : OPE Γ Δ) → comp oid f ≡ f
leftid done       = refl 
leftid (keep σ f) = cong (keep σ)  (leftid f) 
leftid (skip σ f) = cong (skip σ) (leftid f)

-- Variables
oidxmap : ∀ {Γ σ}(x : Var Γ σ) → xmap oid x ≡ x
oidxmap vZ       = refl 
oidxmap (vS σ x) = cong (vS σ) (oidxmap x) 

compxmap : ∀ {B Γ Δ σ}(f : OPE B Γ)(g : OPE Γ Δ)(x : Var Δ σ) → 
           xmap f (xmap g x) ≡ xmap (comp f g) x
compxmap done     done     ()
compxmap (skip σ f) g           x         = cong (vS σ) (compxmap f g x)  
compxmap (keep σ f) (keep .σ g) vZ        = refl 
compxmap (keep σ f) (keep .σ g) (vS .σ x) = cong (vS σ) (compxmap f g x) 
compxmap (keep σ f) (skip .σ g) x         = cong (vS σ) (compxmap f g x) 

-- Values
mutual
  oidvmap : ∀ {Γ σ}(v : Val Γ σ) → vmap oid v ≡ v
  oidvmap (λv t vs) = cong (λv t) (oidemap vs) 
  oidvmap (nev n)   = cong nev (oidnevmap n) 

  oidnevmap : ∀ {Γ σ}(n : NeV Γ σ) → nevmap oid n ≡ n
  oidnevmap (varV x)   = cong varV (oidxmap x) 
  oidnevmap (appV n v) = cong₂ appV (oidnevmap n) (oidvmap v) 
  
  oidemap : ∀ {Γ Δ}(vs : Env Γ Δ) → emap oid vs ≡ vs
  oidemap ε        = refl 
  oidemap (vs << v) = cong₂ _<<_ (oidemap vs) (oidvmap v) 

mutual
  compvmap : ∀ {B Γ Δ σ}(f : OPE B Γ)(g : OPE Γ Δ)(v : Val Δ σ) → 
             vmap f (vmap g v) ≡ vmap (comp f g) v
  compvmap f g (λv t vs) = cong (λv t) (compemap f g vs) 
  compvmap f g (nev n)   = cong nev (compnevmap f g n) 

  compnevmap : ∀ {B Γ Δ σ}(f : OPE B Γ)(g : OPE Γ Δ)(n : NeV Δ σ) → 
               nevmap f (nevmap g n) ≡ nevmap (comp f g) n
  compnevmap f g (varV x)   = cong varV (compxmap f g x) 
  compnevmap f g (appV n v) = cong₂ appV (compnevmap f g n) (compvmap f g v) 

  compemap : ∀ {A B Γ Δ}(f : OPE A B)(g : OPE B Γ)(vs : Env Γ Δ) → 
             emap f (emap g vs) ≡ emap (comp f g) vs
  compemap f g ε         = refl 
  compemap f g (vs << v) = cong₂ _<<_ (compemap f g vs) (compvmap f g v) 

quotlemma : ∀ {Γ Δ σ} τ (f : OPE Γ Δ)(v : Val Δ σ) →
             vmap (keep τ f) (vmap (skip τ oid) v) ≡ vwk τ (vmap f v)
quotlemma τ f v = 
  trans (trans (compvmap (keep τ f) (skip τ oid) v)
                 (cong (λ f → vmap (skip τ f) v)
                       (trans (rightid f) 
                               (sym (leftid f)))))
         (sym (compvmap (skip τ oid) f v))

-- Embedding and conversion
-- Variables
oxemb : ∀ {Γ Δ σ}(f : OPE Γ Δ)(x : Var Δ σ) →
        embˣ (xmap f x) ≈ embˣ x [ oemb f ]
oxemb (keep σ f) vZ       = ≈sym top< 
oxemb (skip σ f) vZ       = ≈trans (cong[] (oxemb f vZ) ≃refl) [][] 
oxemb (keep .τ f) (vS τ x) = 
  ≈trans (cong[] (oxemb f x) ≃refl)
        (≈trans (≈trans [][] (cong[] ≈refl (≃sym popcomp))) (≈sym [][])) 
oxemb (skip σ  f) (vS τ x) = ≈trans (cong[] (oxemb f (vS τ x)) ≃refl) [][] 
oxemb done ()

-- Values
mutual
  ovemb : ∀ {Γ Δ σ}(f : OPE Γ Δ)(v : Val Δ σ) →
            emb (vmap f v) ≈ emb v [ oemb f ]
  ovemb f (λv t vs) = ≈trans (cong[] ≈refl (oeemb f vs)) (≈sym [][]) 
  ovemb f (nev n)   = onevemb f n 

  onevemb : ∀ {Γ Δ σ}(f : OPE Γ Δ)(n : NeV Δ σ) →
            embⁿ (nevmap f n) ≈ embⁿ n [ oemb f ]
  onevemb f (varV x)   = oxemb f x 
  onevemb f (appV n v) = ≈trans (cong$ (onevemb f n) (ovemb f v)) (≈sym $[]) 

  oeemb : ∀ {B Γ Δ}(f : OPE B Γ)(vs : Env Γ Δ) →
           embˢ (emap f vs) ≃ embˢ vs ○ oemb f
  oeemb f (vs << v) = ≃trans (cong< (oeemb f vs) (ovemb f v)) (≃sym comp<) 
  oeemb {Γ = Γ < σ} (keep .σ f) ε = 
    ≃trans (≃trans (≃trans (cong○ (oeemb f ε) ≃refl) assoc) 
                   (cong○ ≃refl (≃sym popcomp))) 
           (≃sym assoc) 
  oeemb {Γ = Γ < σ} (skip τ  f) ε = ≃trans (cong○ (oeemb f ε) ≃refl) assoc 
  oeemb {Γ = ε} done       ε = ≃sym leftidˢ 
  oeemb {Γ = ε} (skip σ f) ε = ≃trans (cong○ (oeemb f ε) ≃refl) assoc 

lemoid : ∀ {Γ} → id {Γ} ≃ oemb oid
lemoid {ε}     = ≃refl 
lemoid {Γ < σ} = ≃trans idcomp (cong< (cong○ (lemoid {Γ}) ≃refl) ≈refl) 

-- Normal Forms
mutual
  onfemb : ∀ {Γ Δ σ}(f : OPE Γ Δ)(n : Nf Δ σ) →
           nemb (nfmap f n) ≈ nemb n [ oemb f ]
  onfemb f (λn n) = ≈trans (congλ (onfemb (keep _ f) n)) (≈sym λ[]) 
  onfemb f (ne n) = onenemb f n 

  onenemb : ∀ {Γ Δ σ}(f : OPE Γ Δ)(n : NeN Δ σ) →
            nembⁿ (nenmap f n) ≈ nembⁿ n [ oemb f ]
  onenemb f (varN x)    = oxemb f x 
  onenemb f (appN n n') = ≈trans (cong$ (onenemb f n) (onfemb f n')) (≈sym $[]) 
