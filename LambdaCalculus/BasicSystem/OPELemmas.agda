module BasicSystem.OPELemmas where

open import BasicSystem.Utils
open import BasicSystem.Syntax
open import BasicSystem.Embeddings
open import BasicSystem.Conversion
open import BasicSystem.OPE

rightid : ∀ {Γ Δ} (f : OPE Γ Δ) → comp f oid ≡ f
rightid done     = refl 
rightid (keep α f) = cong (keep α) (rightid f) 
rightid (skip α f) = cong (skip α) (rightid f)

leftid : ∀ {Γ Δ} (f : OPE Γ Δ) → comp oid f ≡ f
leftid done       = refl 
leftid (keep α f) = cong (keep α)  (leftid f) 
leftid (skip α f) = cong (skip α) (leftid f)

-- Variables
oidxmap : ∀ {Γ α}(x : Var Γ α) → xmap oid x ≡ x
oidxmap zero       = refl 
oidxmap (suc x) = cong suc (oidxmap x) 

compxmap : ∀ {B Γ Δ α}(f : OPE B Γ)(g : OPE Γ Δ)(x : Var Δ α) → 
           xmap f (xmap g x) ≡ xmap (comp f g) x
compxmap done     done     ()
compxmap (skip α f) g           x         = cong suc (compxmap f g x)  
compxmap (keep α f) (keep .α g) zero        = refl 
compxmap (keep α f) (keep .α g) (suc x) = cong suc (compxmap f g x) 
compxmap (keep α f) (skip .α g) x         = cong suc (compxmap f g x) 

-- Values
mutual
  oidvmap : ∀ {Γ α}(v : Val Γ α) → vmap oid v ≡ v
  oidvmap (lam t vs) = cong (lam t) (oidemap vs) 
  oidvmap (ne n)   = cong ne (oidnevmap n) 

  oidnevmap : ∀ {Γ α}(n : NeVal Γ α) → nevmap oid n ≡ n
  oidnevmap (var x)   = cong var (oidxmap x) 
  oidnevmap (app n v) = cong₂ app (oidnevmap n) (oidvmap v) 
  
  oidemap : ∀ {Γ Δ}(vs : Env Γ Δ) → emap oid vs ≡ vs
  oidemap []        = refl 
  oidemap (v ∷ vs) = cong₂ _∷_ (oidvmap v) (oidemap vs) 

mutual
  compvmap : ∀ {B Γ Δ α}(f : OPE B Γ)(g : OPE Γ Δ)(v : Val Δ α) → 
             vmap f (vmap g v) ≡ vmap (comp f g) v
  compvmap f g (lam t vs) = cong (lam t) (compemap f g vs) 
  compvmap f g (ne n)   = cong ne (compnevmap f g n) 

  compnevmap : ∀ {B Γ Δ α}(f : OPE B Γ)(g : OPE Γ Δ)(n : NeVal Δ α) → 
               nevmap f (nevmap g n) ≡ nevmap (comp f g) n
  compnevmap f g (var x)   = cong var (compxmap f g x) 
  compnevmap f g (app n v) = cong₂ app (compnevmap f g n) (compvmap f g v) 

  compemap : ∀ {A B Γ Δ}(f : OPE A B)(g : OPE B Γ)(vs : Env Γ Δ) → 
             emap f (emap g vs) ≡ emap (comp f g) vs
  compemap f g []         = refl 
  compemap f g (v ∷ vs) = cong₂ _∷_ (compvmap f g v) (compemap f g vs) 

quotlemma : ∀ {Γ Δ α} β (f : OPE Γ Δ)(v : Val Δ α) →
             vmap (keep β f) (vmap (skip β oid) v) ≡ vwk β (vmap f v)
quotlemma β f v = 
  trans (trans (compvmap (keep β f) (skip β oid) v)
                 (cong (λ f → vmap (skip β f) v)
                       (trans (rightid f) 
                               (sym (leftid f)))))
         (sym (compvmap (skip β oid) f v))

-- Embedding and conversion
-- Variables
oxemb : ∀ {Γ Δ α}(f : OPE Γ Δ)(x : Var Δ α) →
        embˣ (xmap f x) ≈ embˣ x [ oemb f ]
oxemb (keep α f) zero       = ≈sym ø< 
oxemb (skip α f) zero       = ≈trans (cong[] (oxemb f zero) ≃refl) [][] 
oxemb (keep β f) (suc x) = 
  ≈trans (cong[] (oxemb f x) ≃refl)
        (≈trans (≈trans [][] (cong[] ≈refl (≃sym ↑comp))) (≈sym [][])) 
oxemb (skip α  f) (suc x) = ≈trans (cong[] (oxemb f (suc x)) ≃refl) [][] 
oxemb done ()

-- Values
mutual
  ovemb : ∀ {Γ Δ α}(f : OPE Γ Δ)(v : Val Δ α) →
            emb (vmap f v) ≈ emb v [ oemb f ]
  ovemb f (lam t vs) =
    ≈trans ((ƛ t) [ embˢ (emap f vs) ] ≈ (ƛ t) [ embˢ vs ○ oemb f ] ∋
              cong[] ≈refl (oeemb f vs))
           ((ƛ t) [ embˢ vs ○ oemb f ] ≈ ((ƛ t) [ embˢ vs ]) [ oemb f ] ∋
              ≈sym [][]) 
  ovemb f (ne n)   = onevemb f n 

  onevemb : ∀ {Γ Δ α}(f : OPE Γ Δ)(n : NeVal Δ α) →
            embⁿ (nevmap f n) ≈ embⁿ n [ oemb f ]
  onevemb f (var x)   = oxemb f x 
  onevemb f (app n v) = ≈trans (cong∙ (onevemb f n) (ovemb f v)) (≈sym ∙[]) 

  oeemb : ∀ {B Γ Δ}(f : OPE B Γ)(vs : Env Γ Δ) →
           embˢ (emap f vs) ≃ embˢ vs ○ oemb f
  oeemb f (v ∷  vs) = ≃trans (cong< (oeemb f vs) (ovemb f v)) (≃sym comp<) 
  oeemb {Γ = α ∷ Γ} (keep .α f) [] = 
    ≃trans (≃trans (≃trans (cong○ (oeemb f []) ≃refl) assoc) 
                           (cong○ ≃refl (≃sym ↑comp))) 
           (embˢ [] ○ (↑ ○ (ø ∷ (oemb f ○ ↑))) ≃
              (embˢ [] ○ ↑) ○ (ø ∷ (oemb f ○ ↑)) ∋ ≃sym assoc) 
  oeemb {Γ = α ∷ Γ} (skip β  f) [] =
    ≃trans (embˢ [] ○ (↑) ≃
                 ((embˢ [] ○ ↑) ○ oemb f) ○ ↑ ∋ cong○ (oeemb f []) ≃refl)
           (((embˢ [] ○ ↑) ○ oemb f) ○ ↑ ≃
                   (embˢ [] ○ ↑) ○ (oemb f ○ ↑) ∋ assoc) 
  oeemb {Γ = []} done       [] = ≃sym leftidˢ 
  oeemb {Γ = []} (skip α f) [] =
    ≃trans (embˢ [] ○ ↑ ≃ (ı ○ oemb f) ○ ↑
                 ∋ cong○ (oeemb f []) ≃refl)
           ((ı ○ oemb f) ○ ↑ ≃ ı ○ (oemb f ○ ↑)
                 ∋ assoc)

lemoid : ∀ {Γ} → ı {Γ} ≃ oemb oid
lemoid {[]}     = ≃refl 
lemoid {α ∷ Γ} = ≃trans idcomp (cong< (cong○ (lemoid {Γ}) ≃refl) ≈refl) 

-- Normal Forms
mutual
  onfemb : ∀ {Γ Δ α}(f : OPE Γ Δ)(n : Nf Δ α) →
           nemb (nfmap f n) ≈ nemb n [ oemb f ]
  onfemb f (lam n) = ≈trans (congλ (onfemb (keep _ f) n)) (≈sym λ[]) 
  onfemb f (ne n) = onenemb f n 

  onenemb : ∀ {Γ Δ α}(f : OPE Γ Δ)(n : NeNf Δ α) →
            nembⁿ (nenmap f n) ≈ nembⁿ n [ oemb f ]
  onenemb f (var x)    = oxemb f x 
  onenemb f (app n n') = ≈trans (cong∙ (onenemb f n) (onfemb f n')) (≈sym ∙[]) 
