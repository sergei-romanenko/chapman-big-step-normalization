module BasicSystem.Soundness where

open import BasicSystem.Utils
open import BasicSystem.Syntax
open import BasicSystem.Conversion
open import BasicSystem.OPE
open import BasicSystem.OPELemmas
open import BasicSystem.IdentityEnvironment
open import BasicSystem.RecursiveNormaliser
open import BasicSystem.OPERecursive
open import BasicSystem.StrongConvertibility

mutual
  idext : ∀ {Γ Δ α}(t : Tm Δ α){vs vs' : Env Γ Δ} → vs ∼ˢ vs' →
          eval t vs ∼ eval t vs'
  idext ø              (∼<< p q) = q 
  idext (t [ ts ])       p         = idext t (idextˢ ts p)
  idext (ƛ t)           p         = λ f p' → idext t (∼<< (∼ˢmap f p) p')   
  idext (t ∙ u){vs}{vs'} p         = 
    helper (sym (oidvmap (eval t vs))) 
           (sym (oidvmap (eval t vs'))) 
           (idext t p oid (idext u p)) 

  idextˢ : ∀ {B Γ Δ}(ts : Sub Γ Δ){vs vs' : Env B Γ} → vs ∼ˢ vs' →
           evalˢ ts vs ∼ˢ evalˢ ts vs' 
  idextˢ ↑   (∼<< p q) = p 
  idextˢ (t ∷ ts)  p         = ∼<< (idextˢ ts p) (idext t p) 
  idextˢ ı        p         = p 
  idextˢ (ts ○ us) p         = idextˢ ts (idextˢ us p)

mutual
  sfundthrm : ∀ {Γ Δ α}{t t' : Tm Δ α} → t ≈ t' →
              {vs vs' : Env Γ Δ} → vs ∼ˢ vs' → eval t vs ∼ eval t' vs'
  sfundthrm {t = t} ≈refl q = idext t q
  sfundthrm (≈sym p)       q = sym∼ (sfundthrm p (sym∼ˢ q)) 
  sfundthrm (≈trans p p')  q = 
    trans∼ (sfundthrm p (trans∼ˢ q (sym∼ˢ q))) 
           (sfundthrm p' q)  
  sfundthrm (cong[] p p') q = sfundthrm p (sfundthrmˢ p' q) 
  sfundthrm (congλ p)     q = λ f p' → sfundthrm p (∼<< (∼ˢmap f q) p')  
  sfundthrm (cong∙ {t = t}{t' = t'}{u = u}{u' = u'} p p') {vs} {vs'} q = 
    helper (eval t vs ≡ vmap oid (eval t vs) ∋ sym (oidvmap (eval t  _)))
           (eval t' vs' ≡ vmap oid (eval t' vs') ∋ sym (oidvmap (eval t' _)))
           ((vmap oid (eval t vs) ∙∙ eval u vs) ∼
              (vmap oid (eval t' vs') ∙∙ eval u' vs')
              ∋ sfundthrm p q oid (eval u vs ∼ eval u' vs' ∋ sfundthrm p' q)) 
  sfundthrm {t' = t'} ø<          q = idext t' q 
  sfundthrm {t = t [ ts ] [ us ]} [][]          q = idext t (idextˢ ts (idextˢ us q))  
  sfundthrm {t' = t} []id          q = idext t q 
  sfundthrm (λ[] {t = t}{ts = ts}){vs}{vs'} q = λ f p → 
    helper' {t = t}
            (evˢmaplem f ts vs') 
            (idext t (∼<< (∼ˢmap f (idextˢ ts q)) p)) 
  sfundthrm (∙[]{t = t}{u = u}{ts = ts}) q =
    helper (sym (oidvmap (eval t (evalˢ ts _))))
           (sym (oidvmap (eval t (evalˢ ts _))))
           (idext t (idextˢ ts q) oid (idext u (idextˢ ts q))) 
  sfundthrm (≈βσ {t = t}{u = u}) q = idext t (∼<< q (idext u q)) 
  sfundthrm (≈η {t = t}){vs = vs}{vs' = vs'} q = λ f {a} {a'} p → 
    helper {f = vmap f (eval t vs)} 
           refl
           (evmaplem f t vs')
           (idext t q f p)

  sfundthrmˢ : ∀ {B Γ Δ}{ts ts' : Sub Γ Δ} → ts ≃ ts' →
               {vs vs' : Env B Γ} → vs ∼ˢ vs' → evalˢ ts vs ∼ˢ evalˢ ts' vs'
  sfundthrmˢ {ts = ts} ≃refl         q = idextˢ ts q 
  sfundthrmˢ (≃sym p)      q = sym∼ˢ (sfundthrmˢ p (sym∼ˢ q)) 
  sfundthrmˢ (≃trans p p') q = 
    trans∼ˢ (sfundthrmˢ p (trans∼ˢ q (sym∼ˢ q)))
             (sfundthrmˢ p' q)  
  sfundthrmˢ (cong< p p')  q = ∼<< (sfundthrmˢ p q) (sfundthrm p' q) 
  sfundthrmˢ (cong○ p p')  q = sfundthrmˢ p (sfundthrmˢ p' q ) 
  sfundthrmˢ idcomp        (∼<< q q') = ∼<< q q' 
  sfundthrmˢ {ts' = ts} ↑comp       q = idextˢ ts q 
  sfundthrmˢ {ts' = ts} leftidˢ       q = idextˢ ts q 
  sfundthrmˢ {ts' = ts} rightidˢ      q = idextˢ ts q 
  sfundthrmˢ {ts = (ts ○ ts') ○ ts''} assoc         q = idextˢ ts (idextˢ ts' (idextˢ ts'' q)) 
  sfundthrmˢ {ts = (t ∷ ts) ○ ts'} comp<         q = 
   ∼<< (idextˢ ts (idextˢ ts' q)) (idext t (idextˢ ts' q)) 

mutual
  squotelema : ∀ {Γ α}{v v' : Val Γ α} → 
               v ∼ v' → quot v ≡ quot v'
  squotelema {α = ⋆}    {ne n}{ne n'} p = cong ne p 
  squotelema {Γ}{α ⇒ β}                p = 
    cong lam (squotelema {α = β} (p (weak α) q)) 
    where
    q = squotelemb refl

  squotelemb : ∀ {Γ α}{n n' : NeVal Γ α} → 
               quotⁿ n ≡ quotⁿ n' → ne n ∼ ne n'
  squotelemb {α = ⋆}     p = p 
  squotelemb {α = α ⇒ β}{n}{n'} p = λ f q → 
    let q' = squotelema {α = α} q     
    in  squotelemb {α = β} 
                   (cong₂ app 
                          (trans (qⁿmaplem f n) 
                                  (trans (cong (nenmap f) p) 
                                          (sym (qⁿmaplem f n')))) 
                          q')   

sndvar : ∀ {Γ α}(x : Var Γ α) → ne (var x) ∼ ne (var x)
sndvar x = squotelemb refl 

sndid : ∀ Γ → (vid {Γ}) ∼ˢ (vid {Γ})
sndid []       = ∼[] 
sndid (α ∷ Γ) = ∼<< (∼ˢmap (skip α oid) (sndid Γ)) (sndvar zero) 

soundthrm : ∀ {Γ α}{t t' : Tm Γ α} → t ≈ t' → nf t ≡ nf t'
soundthrm {Γ}{α} p = squotelema {α = α} (sfundthrm p (sndid Γ)) 
