module NaturalNumbers.Soundness where
open import NaturalNumbers.Utils
open import NaturalNumbers.Syntax
open import NaturalNumbers.OPE
open import NaturalNumbers.OPELemmas
open import NaturalNumbers.OPERecursive
open import NaturalNumbers.RecursiveNormaliser
open import NaturalNumbers.Conversion
open import NaturalNumbers.StrongConvertibility
open import NaturalNumbers.IdentityEnvironment

mutual
  squotlema : ∀ {Γ σ}{v v' : Val Γ σ} → 
               v ∼ v' → quot v ≡ quot v'
  squotlema {σ = ⋆}    {nev n}{nev n'} p = cong ne⋆ p 
  squotlema {Γ}{σ ⇒ τ}                 p = 
    cong λn (squotlema {σ = τ} (p (weak σ) q)) 
    where
    q = squotlemb refl
  squotlema {Γ} {N} ∼zero    = refl 
  squotlema {Γ} {N} (∼suc p) = cong sucn (squotlema {σ = N} p) 
  squotlema {Γ} {N} (∼nev p) = cong neN p 

  squotlemb : ∀ {Γ σ}{n n' : NeV Γ σ} → 
               quotⁿ n ≡ quotⁿ n' → nev n ∼ nev n'
  squotlemb {σ = ⋆}     p = p 
  squotlemb {σ = σ ⇒ τ}{n}{n'} p = λ f q → 
    let q' = squotlema {σ = σ} q     
    in  squotlemb {σ = τ} 
                   (cong₂ appN 
                          (trans (qⁿmaplem f n) 
                                  (trans (cong (nenmap f) p) 
                                          (sym (qⁿmaplem f n')))) 
                          q')   
  squotlemb {σ = N} p = ∼nev p  

sndvar : ∀ {Γ σ}(x : Var Γ σ) → nev (varV x) ∼ nev (varV x)
sndvar x = squotlemb refl

sndid : ∀ Γ → (vid {Γ}) ∼ˢ (vid {Γ})
sndid ε       = ∼ε 
sndid (Γ < σ) = ∼<< (∼ˢmap (skip σ oid) (sndid Γ)) (sndvar vZ) 

primlem : ∀ {Γ σ}{z z' : Val Γ σ}{s s' : Val Γ (N ⇒ σ ⇒ σ)}{v v' : Val Γ N} → 
          z ∼ z' → s ∼ s' → v ∼ v' →
          vprim z s v ∼ vprim z' s' v'
primlem p p' ∼zero    = p 
primlem {s = s}{s'}{sucv v}{sucv v'} p p' (∼suc p'') with p' oid p'' oid (primlem {s = s}{s'} p p' p'')
... | q with vmap oid s | oidvmap s | vmap oid s' | oidvmap s'
... | ._ | refl | ._ | refl with vmap oid (s ∙∙ v) | oidvmap (s ∙∙ v) | vmap oid (s' ∙∙ v') | oidvmap (s' ∙∙ v') 
... | ._ | refl | ._ | refl = q 
primlem {σ = σ} p p' (∼nev p'') =
  squotlemb (cong₃ primN 
                    (squotlema p) 
                    (cong (λ n → λn (λn n)) 
                          (squotlema (p' (weak N) (sndvar (vZ {σ = N})) (weak σ) (sndvar (vZ {σ = σ}))))) 
                    p'')  


mutual
  idext : ∀ {Γ Δ σ}(t : Tm Δ σ){vs vs' : Env Γ Δ} → vs ∼ˢ vs' →
          eval t vs ∼ eval t vs'
  idext ø              (∼<< p q) = q 
  idext (t [ ts ])       p         = idext t (idextˢ ts p)
  idext (ƛ t)            p         = λ f p' → idext t (∼<< (∼ˢmap f p) p')   
  idext (t ∙ u){vs}{vs'} p         = 
    helper (sym (oidvmap (eval t vs))) 
           (sym (oidvmap (eval t vs'))) 
           (idext t p oid (idext u p)) 
  idext zero             p         = ∼zero 
  idext (suc t)          p         = ∼suc (idext t p)  
  idext (prim z s t)     p         = primlem (idext z p) (idext s p) (idext t p)

  idextˢ : ∀ {B Γ Δ}(ts : Sub Γ Δ){vs vs' : Env B Γ} → vs ∼ˢ vs' →
           evalˢ ts vs ∼ˢ evalˢ ts vs' 
  idextˢ (↑ σ)   (∼<< p q) = p 
  idextˢ (ts < t)  p         = ∼<< (idextˢ ts p) (idext t p) 
  idextˢ ı        p         = p 
  idextˢ (ts ○ us) p         = idextˢ ts (idextˢ us p)

mutual
  sfundthrm : ∀ {Γ Δ σ}{t t' : Tm Δ σ} → t ≈ t' →
              {vs vs' : Env Γ Δ} → vs ∼ˢ vs' → eval t vs ∼ eval t' vs'
  sfundthrm {t = t} ≈refl  q = idext t q
  sfundthrm (≈sym p)       q = sym∼ (sfundthrm p (sym∼ˢ q)) 
  sfundthrm (≈trans p p')  q = 
    trans∼ (sfundthrm p (trans∼ˢ q (sym∼ˢ q))) 
           (sfundthrm p' q)  
  sfundthrm (cong[] p p') q = sfundthrm p (sfundthrmˢ p' q) 
  sfundthrm (congλ p)     q = λ f p' → sfundthrm p (∼<< (∼ˢmap f q) p')  
  sfundthrm (cong∙ {t = t}{t' = t'} p p')  q = 
    helper (sym (oidvmap (eval t  _)))
           (sym (oidvmap (eval t' _)))
           (sfundthrm p q oid (sfundthrm p' q)) 
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
  sfundthrm (β {t = t}{u = u}) q = idext t (∼<< q (idext u q)) 
  sfundthrm (η {t = t}){vs = vs}{vs' = vs'} q = λ f {a} {a'} p → 
    helper {f = vmap f (eval t vs)} 
           refl
           (evmaplem f t vs')
           (idext t q f p) 
  sfundthrm (congsuc p)         q = ∼suc (sfundthrm p q) 
  sfundthrm (congprim p p' p'') q = primlem (sfundthrm p q) (sfundthrm p' q) (sfundthrm p'' q)  
  sfundthrm zero[]              p = ∼zero 
  sfundthrm (suc[] {t = t}{ts}) p = ∼suc (idext t (idextˢ ts p) ) 
  sfundthrm (prim[] {z = z}{s}{t}{ts}) p = 
    primlem (idext z (idextˢ ts p)) (idext s (idextˢ ts p)) (idext t (idextˢ ts p)) 
  sfundthrm (primz {z = t})     p = idext t p 
  sfundthrm (prims {z = z}{s}{t}){vs}{vs'} p with idext s p oid (idext t p) oid (primlem {s = eval s vs}{eval s vs'}(idext z p) (idext s p) (idext t p))
  ... | q with vmap oid (eval s vs) | oidvmap (eval s vs)  | vmap oid (eval s vs') | oidvmap (eval s vs') 
  ... | ._ | refl | ._ | refl with vmap oid (eval s vs ∙∙ eval t vs) | oidvmap (eval s vs ∙∙ eval t vs) | vmap oid (eval s vs' ∙∙ eval t vs') | oidvmap (eval s vs' ∙∙ eval t vs')
  ... | ._ | refl | ._ | refl = q 

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
  sfundthrmˢ {ts = (ts < t) ○ ts'} comp<         q = 
   ∼<< (idextˢ ts (idextˢ ts' q)) (idext t (idextˢ ts' q)) 

soundthrm : ∀ {Γ σ}{t t' : Tm Γ σ} → t ≈ t' → nf t ≡ nf t'
soundthrm {Γ}{σ} p = squotlema {σ = σ} (sfundthrm p (sndid Γ)) 
