import data.real.basic
import tactic.suggest
import mainDef

namespace basic_real_analysis
-- * --------------Finis------------------------- * --
lemma lipschitzienne_imp_ucontinue (f : ℝ → ℝ) : is_lipschitzienne f → is_ucontinuous f :=
begin
  intro h,
  cases h with k hk,
  assume ε>0,
  let η := ε / k,
  use η,
  split,

  cases hk with hk1 hk,
  exact div_pos H hk1,

  intros x y h,
  cases hk with k_pos hf,
  have h₁ : |f x - f y| ≤ k * |x - y| := hf x y, -- hf needed x and y to be true
  have h₂ : k * |x - y| ≤ k * η :=  mul_le_mul_of_nonneg_left h (le_of_lt k_pos), -- merci chatGPT
  have h₃ : k*η = ε := eq.symm _,
  calc |f x - f y| ≤ k * |x - y| : h₁
                 ... ≤ k * η     : h₂
                 ... = ε         : h₃,
  apply eq_comm.mp _,
  calc k * η = k * (ε / k) : refl _
         ... = ε : _ ,

  have h₄ : k ≠ 0 := ne_of_gt k_pos,
  have k_ne_zero : k ≠ 0,
  apply h₄,
  rw mul_div_cancel' ε h₄,  
end

theorem converge_imp_cauchy (u : ℕ → ℝ) : u_converge u → is_cauchy u :=
begin
  intros h_converge,
  cases h_converge with l hl,
  intros ε hε,
  cases hl (ε / 2) (half_pos hε) with N hN, -- Use hl and prove eps/2 is positive
  use N,
  intros p q hpq,
  cases hpq with hp hq,
  calc |u p - u q| = |(u p - l) + (l - u q)| : by ring_nf
  ... ≤ |u p - l| + |l - u q| : abs_add _ _ -- inégalité triangulaire : (u p - l) (l - u q
  ... ≤ ε / 2 + ε / 2 : add_le_add _ _
  ... = ε : add_halves ε,
  
  exact hN p hp,
  rw abs_sub_comm,
  exact hN q hq,
end


-- * --------------En cours------------------------- * --
-- Si U_n monotone & borné -> converge
lemma u_converge_if_bounded_monotone (u : ℕ → ℝ) (h1 : is_ubounded u) (h2 : is_monotone_real u) : u_converge u :=
begin
  split,
  have H := h1,
  assume e>0,
  -- unfold is_monotone_real at h2,
  
  -- cases h1 with a b,
  -- rcases H with ⟨M, hM, hM'⟩,
  sorry -- https://en.wikipedia.org/wiki/Monotone_convergence_theorem
end


theorem bolzano_weierstrass (a : ℕ → ℝ) (ha : is_ubounded a) : ∃ (b : ℕ → ℝ) (hb : is_subsequence_of a b), u_converge b :=
begin 
  cases ha with M hM,
  apply bex_def.mpr _,
  apply bex_def.mp _,
  -- let b : ℕ → ℝ, -- je sais pas comment dire qu'elle existe
  use b,
  have hb : is_subsequence_of a b,
  sorry, -- ce sorry vient du premier, donc ca passe

  split,
  apply hb,
  have hb_bounded : is_ubounded b,
  sorry, -- là aucune idée de montrer implicitement la relation avec a
  have hb_monotone : is_monotone_real b,
  use u_has_subsequence_monotone a b hb,
  use u_converge_if_bounded_monotone b hb_bounded hb_monotone,
end

-- * --------------Bonne chance mdr------------------------- * --
-- Royer : https://moodle.univ-tlse3.fr/pluginfile.php/667429/mod_resource/content/4/Bolzano-Weierstrass.pdf
lemma u_has_subsequence_monotone (u : ℕ → ℝ) (v : ℕ → ℝ) (hu : is_subsequence_of u v) : (is_monotone_real v) :=
begin
  sorry -- on va rire si on veut montrer ça mdrrr
end


-- ! ICI
-- file:///C:/Users/admin-lgc/Downloads/23aLectureProofs10.13.15-1.pdf
lemma cauchy_imp_bounded (u : ℕ → ℝ) : is_cauchy u → is_ubounded u :=
begin
  intro h,
  unfold is_cauchy at h,
  unfold is_ubounded,
  cases h 1 _ with N hN,

  choose p hp using exists_nat_ge N,
  let q := N+1,
  have h_ineg : |u p| ≤ 1 + |u (N+1)| := 
  begin
    calc |u p| = |u p - u q + u q| : by ring_nf
    ... ≤  |u p - u q| + |u q| : abs_add (u p - u q) (u q)
    ... ≤  1 + |u q| : add_le_add  _ _
    ... = 1 + |u (N+1)| : by refl,
    
    apply hN,
    split,
    exact hp,
    simp,
  end,

  use (1 + |u (N+1)|), -- là je pense m'être trompé...
  -- je pensais que ç'allait fonctionner mais en fait je bloque un peu trop au deuximèe sorry
  -- la vraie preuve c'est le max de |u 0|, |u 1|, ..., |u N|, |u (N+1)| 
  -- sauf que j'arrive pas à définir un n inférieur à N comme ce que j'ai fait avant et je sais pas pourquoi
  -- choose p hp using exists_nat_ge N, 
  split,
  have h₁ : 0 < 1 := zero_lt_one,
  have h₂ : |u (N+1)| ≥ 0 := abs_nonneg _,
  
  sorry, -- easy to prove ! (mais j'y arrive pas mdr)
  intro n,
  
  sorry -- c'est là que je bloque

  
end


-- theorem cauchy_imp_converge (u : ℕ → ℝ) :  is_cauchy u →  u_converge u :=
-- begin
--   intro h,
--   unfold is_cauchy at h,
--   unfold u_converge,
-- end



end basic_real_analysis
