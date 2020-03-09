theory LinguaFrancaTests

imports LinguaFrancaClocks

begin

section \<open>Tests\<close>

abbreviation \<open>c1::clock \<equiv> (\<lambda>t. t \<ge> 1 \<and> (t-1) mod 2 = 0)\<close>
abbreviation \<open>c2::clock \<equiv> (\<lambda>t. t \<ge> 2 \<and> (t-2) mod 3 = 0)\<close>

value \<open>c1 0\<close>
value \<open>c1 1\<close>
value \<open>c1 2\<close>
value \<open>c1 3\<close>

value \<open>c2 0\<close>
value \<open>c2 1\<close>
value \<open>c2 2\<close>
value \<open>c2 3\<close>
value \<open>c2 4\<close>
value \<open>c2 5\<close>

lemma \<open>kp_periodic 1 2 c1\<close>
  using kp_periodic_def by simp

lemma \<open>kp_periodic 2 3 c2\<close>
  using kp_periodic_def by simp

abbreviation \<open>c3 \<equiv> c1 \<oplus> c2\<close>

value \<open>map c1 [0,1,2,3,4,5,6,7,8,9,10]\<close>
value \<open>map ($c1) [0,1,2,3,4,5,6,7,8,9,10,11]\<close>
value \<open>map c2 [0,1,2,3,4,5,6,7,8,9,10]\<close>
value \<open>map c3 [0,1,2,3,4,5,6,7,8,9,10]\<close>

lemma interv_2:\<open>{t::nat. t\<^sub>0 \<le> t \<and> t < t\<^sub>0 + 2 \<and> 1 \<le> t \<and> (t - 1) mod 2 = 0} = {t. (t = t\<^sub>0 \<or> t = t\<^sub>0 + 1) \<and> 1 \<le> t \<and> (t - 1) mod 2 = 0}\<close>
  by auto

lemma \<open>bounded 2 1 c1\<close>
proof -
  have \<open>\<forall>t. tick_count c1 t 2 \<le> 1\<close>
  proof -
    { fix t\<^sub>0::nat
      have \<open>tick_count c1 t\<^sub>0 2 \<le> 1\<close>
      proof (cases t\<^sub>0)
        case 0
          hence \<open>tick_count c1 t\<^sub>0 2 = ticks_up_to c1 1\<close>
            using tick_count_orig by (simp add: numeral_2_eq_2)
          also have \<open>... = card {t::nat. t \<le> 1 \<and> 1 \<le> t \<and> (t-1) mod 2 = 0}\<close>
            unfolding ticks_up_to_def by simp
          also have \<open>... \<le>  card {t::nat. t \<le> 1 \<and> 1 \<le> t}\<close>
            by (metis (mono_tags, lifting) Collect_cong
                cancel_comm_monoid_add_class.diff_cancel le_antisym le_refl mod_0)
          also have \<open>... = card {t::nat. t = 1}\<close> by (metis le_antisym order_refl)
          also have \<open>... = 1\<close> by simp
          finally show ?thesis . 
      next
        case (Suc nat)
          then show ?thesis
          proof (cases \<open>(t\<^sub>0-1) mod 2 = 0\<close>)
            case True
              with Suc have \<open>t\<^sub>0 mod 2 \<noteq> 0\<close> by arith 
              hence \<open>{t. (t = t\<^sub>0 \<or> t = t\<^sub>0 + 1) \<and> 1 \<le> t \<and> (t - 1) mod 2 = 0} = {t\<^sub>0}\<close>
                using True  by auto
              hence \<open>{t. t\<^sub>0 \<le> t \<and> t < t\<^sub>0 + 2 \<and> 1 \<le> t \<and> (t - 1) mod 2 = 0} = {t\<^sub>0}\<close>
                using interv_2 by simp
              thus ?thesis unfolding tick_count_def by simp
          next
            case False
              with Suc have \<open>t\<^sub>0 mod 2 = 0\<close> by arith
              hence \<open>{t. (t = t\<^sub>0 \<or> t = t\<^sub>0 + 1) \<and> 1 \<le> t \<and> (t - 1) mod 2 = 0} = {t\<^sub>0+1}\<close>
                by auto 
              hence \<open>{t. t\<^sub>0 \<le> t \<and> t < t\<^sub>0 + 2 \<and> 1 \<le> t \<and> (t - 1) mod 2 = 0} = {t\<^sub>0+1}\<close>
                using interv_2 by simp
              thus ?thesis unfolding tick_count_def by simp
          qed
      qed
    }
    thus ?thesis ..
  qed
  thus ?thesis using bounded_def by simp
qed

end
