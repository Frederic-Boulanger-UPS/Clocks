theory LinguaFrancaLogicalTime

imports LinguaFrancaClocks

begin

section \<open>Logical time\<close>

text \<open>
Logical time is a natural number that is attached to instants.
Logical time can stay constant for an arbitrary number of instants, but it cannot decrease.
When logical time stays constant for an infinite number of instants, we have a Zeno condition.
\<close>

typedef time = \<open>{t::nat\<Rightarrow>nat. mono t}\<close>
  using mono_Suc by blast

setup_lifting type_definition_time

text \<open>
A chronometric clock is a clock associated with a time line.
\<close>
type_synonym chronoclock = \<open>clock\<times>time\<close>

text \<open>
@term{\<open>c \<nabla> t\<close>} tells whether chronometric clock @{term c} ticks at instant @{term t}.
\<close>
definition ticks :: \<open>[chronoclock, nat] \<Rightarrow> bool\<close> (infix \<open>\<nabla>\<close> 60)
  where \<open>c \<nabla> t \<equiv> (fst c) t\<close>


text \<open>
@term{\<open>c\<^bsub>t\<^esub>\<close>} is the logical time on clock @{term c} at instant @{term t}.
\<close>
lift_definition time_at :: \<open>[chronoclock, nat] \<Rightarrow> nat\<close> (\<open>_\<^bsub>_\<^esub>\<close> [60, 60])
  is \<open>\<lambda>c t. (snd c) t\<close> .

lemmas chronoclocks_simp[simp] = ticks_def time_at_def

text \<open>
As consequence of the definition of the @{type \<open>time\<close>} type, @{term \<open>(\<nabla>)\<close>} is monotonous for any clock.
\<close>
lemma mono_chronotime:
  \<open>mono (time_at c)\<close> using Rep_time by auto

text \<open>
An event occurs at a given time if the clock ticks at some instant at that time.
\<close>
definition occurs :: \<open>[nat, chronoclock] \<Rightarrow> bool\<close>
  where \<open>occurs n c \<equiv> \<exists>k. (c \<nabla> k \<and> c\<^bsub>k\<^esub> = n)\<close>

text \<open>
An event occurs once at a given time if the clock ticks at exactly one instant at that time.
\<close>
definition occurs_once :: \<open>[nat, chronoclock] \<Rightarrow> bool\<close>
  where \<open>occurs_once n c \<equiv> \<exists>!k. (c \<nabla> k \<and> c\<^bsub>k\<^esub> = n)\<close>

lemma occurs_once_occurs:
  \<open>occurs_once n c \<Longrightarrow> occurs n c\<close>
unfolding occurs_once_def occurs_def by blast

text \<open>
A clock is strict at a given time if it ticks at most once at that time.
\<close>
definition strict_at :: \<open>[nat, chronoclock] \<Rightarrow> bool\<close>
  where \<open>strict_at n c \<equiv> (occurs n c \<longrightarrow> occurs_once n c)\<close>

definition strict_clock :: \<open>chronoclock \<Rightarrow> bool\<close>
  where \<open>strict_clock c \<equiv> (\<forall>n. strict_at n c)\<close>

subsection \<open>Chrono-periodic and chrono-sporadic clocks\<close>
text \<open>
The introduction of logical time allows us to define periodicity and sporadicity
on logical time instead of instant index.
\<close>
definition kp_chronoperiodic :: \<open>[nat, nat, chronoclock] \<Rightarrow> bool\<close>
  where \<open>kp_chronoperiodic k p c \<equiv> (p > 0) \<and> (\<forall>n. occurs n c = ((n \<ge> k) \<and> ((n - k) mod p = 0)))\<close>

definition p_chronoperiodic :: \<open>[nat, chronoclock] \<Rightarrow> bool\<close>
  where \<open>p_chronoperiodic p c \<equiv> \<exists>k. kp_chronoperiodic k p c\<close>

definition chronoperiodic :: \<open>[chronoclock] \<Rightarrow> bool\<close>
  where \<open>chronoperiodic c \<equiv> \<exists>p. p_chronoperiodic p c\<close>

text \<open>
A clock is strictly chronoperiodic if it ticks only once at the logical times when it ticks.
\<close>
definition chronoperiodic_strict :: \<open>[chronoclock] \<Rightarrow> bool\<close>
  where \<open>chronoperiodic_strict c \<equiv> chronoperiodic c \<and> strict_clock c\<close>

definition p_chronoperiodic_strict :: \<open>[nat, chronoclock] \<Rightarrow> bool\<close>
  where \<open>p_chronoperiodic_strict p c \<equiv> p_chronoperiodic p c \<and> strict_clock c\<close>

lemma \<open>chronoperiodic_strict c \<Longrightarrow> chronoperiodic c\<close>
  unfolding chronoperiodic_strict_def by simp

definition p_chronosporadic :: \<open>[nat, chronoclock] \<Rightarrow> bool\<close>
  where \<open>p_chronosporadic p c \<equiv>
    \<forall>t. occurs t c \<longrightarrow> (\<forall>t'. (t' > t \<and> occurs t' c) \<longrightarrow> t' > t + p)\<close>

definition \<open>p_chronosporadic_strict p c \<equiv> p_chronosporadic p c \<and> strict_clock c\<close>

definition \<open>chronosporadic c \<equiv> (\<exists>p > 0. p_chronosporadic p c)\<close>

definition \<open>chronosporadic_strict c \<equiv> chronosporadic c \<and> strict_clock c\<close>

lemma chrono_periodic_suc_sporadic:
  assumes \<open>p_chronoperiodic (p+1) c\<close>
    shows \<open>p_chronosporadic p c\<close>
proof -
  from assms p_chronoperiodic_def obtain k
    where \<open>kp_chronoperiodic k (p+1) c\<close> by blast
  hence *:\<open>\<forall>n. occurs n c = ((n \<ge> k) \<and> ((n - k) mod (p+1) = 0))\<close>
    unfolding kp_chronoperiodic_def by simp
  with mod_offset_sporadic'[of k _ \<open>p+1\<close>] have 
    \<open>\<forall>n. occurs n c \<longrightarrow> (\<forall>n'. (n < n' \<and> ((n'-k) mod (p+1) = 0)) \<longrightarrow> n' \<ge> n+p+1)\<close>
  by simp
  thus ?thesis unfolding p_chronosporadic_def by (simp add: "*" Suc_le_lessD)
qed

lemma chrono_periodic_suc_sporadic_strict:
  assumes \<open>p_chronoperiodic_strict (p+1) c\<close>
    shows \<open>p_chronosporadic_strict p c\<close>
  using assms chrono_periodic_suc_sporadic
        p_chronoperiodic_strict_def p_chronosporadic_strict_def
  by simp

text \<open>
Number of ticks up to a given logical time.
This counts distinct ticks that happen at the same logical time.
\<close>
definition chrono_dense_up_to ::\<open>[chronoclock, nat] \<Rightarrow> nat\<close>
  where \<open>chrono_dense_up_to c n = card {t. c\<^bsub>t\<^esub> \<le> n \<and> c \<nabla> t}\<close>

text \<open>
A clock is Zeno if it ticks an infinite number of times in a finite amount of time.
\<close>
definition zeno_clock :: \<open>chronoclock \<Rightarrow> bool\<close>
  where \<open>zeno_clock c \<equiv> (\<exists>\<omega>. infinite {t. c\<^bsub>t\<^esub> \<le> \<omega> \<and> c \<nabla> t})\<close>

text \<open>
Number of occurrences of an event up to a given logical time.
This does not count separately ticks that occur at the same logical time.
\<close>
definition chrono_up_to ::\<open>[chronoclock, nat] \<Rightarrow> nat\<close>
  where \<open>chrono_up_to c n = card {t. t \<le> n \<and> occurs t c}\<close>

lemma chrono_up_to_bounded:
  \<open>chrono_up_to c n \<le> n+1\<close>
proof -
  have bound:\<open>card {t. t \<le> n} = n+1\<close> using Suc_eq_plus1 card_Collect_le_nat by simp
  hence finite:\<open>finite {t. t \<le> n}\<close> by simp
  have included:\<open>{t. t \<le> n \<and> occurs t c} \<subseteq> {t. t \<le> n}\<close> by blast
  from card_mono[OF finite included] bound
    show ?thesis unfolding chrono_up_to_def by simp
qed


text \<open>
For any time n, a non Zeno clock has less occurrences than ticks up to n.
This is also true for Zeno clock, but we count ticks and occurrences using @{term \<open>card\<close>},
and in Isabelle/HOL, the cardinal of an infinite set is 0, so the inequality breaks when
there are infinitely many ticks before a given time.
\<close>
lemma not_zeno_sparse:
  assumes \<open>\<not>zeno_clock c\<close>
    shows \<open>chrono_up_to c n \<le> chrono_dense_up_to c n\<close>
proof -
  from assms have \<open>finite {t. c\<^bsub>t\<^esub> \<le> n \<and> c \<nabla> t}\<close>
    unfolding zeno_clock_def by simp
  moreover from occurs_def have
    \<open>\<exists>f. \<forall>t. t \<le> n \<and> occurs t c \<longrightarrow>
        (\<exists>k. f k = t \<and> c\<^bsub>k\<^esub> \<le> n \<and> c \<nabla> k)\<close> by auto
  hence
    \<open>\<exists>f. \<forall>t \<in> {t. t \<le> n \<and> occurs t c}.
          \<exists>k. f k = t \<and> k \<in> {k. c\<^bsub>k\<^esub> \<le> n \<and> c \<nabla> k}\<close> by simp
  hence \<open>\<exists>f. {t. t \<le> n \<and> occurs t c} \<subseteq> image f {k. c\<^bsub>k\<^esub> \<le> n \<and> c \<nabla> k}\<close>
    by fastforce
  ultimately have \<open>card {t. t \<le> n \<and> occurs t c} \<le> card {k. c\<^bsub>k\<^esub> \<le> n \<and> c \<nabla> k}\<close>
    using  surj_card_le by blast
  thus ?thesis
    unfolding chrono_up_to_def chrono_dense_up_to_def occurs_def by simp
qed

text \<open>Number of event occurrences during a time window.\<close>
definition occurrence_count :: \<open>[chronoclock, nat, nat] \<Rightarrow> nat\<close>
  where \<open>occurrence_count c t\<^sub>0 d \<equiv> card {t. t\<^sub>0 \<le> t \<and> t < t\<^sub>0 + d \<and> occurs t c}\<close>

text \<open>The number of event occurrences is monotonous with regard to the window width.\<close>
lemma occ_count_mono:
  assumes \<open>d' \<ge> d\<close>
    shows \<open>occurrence_count c t\<^sub>0 d' \<ge> occurrence_count c t\<^sub>0 d\<close>
proof -
  have finite: \<open>finite {t::nat. t\<^sub>0 \<le> t \<and> t < t\<^sub>0+d' \<and> occurs t c}\<close> by simp
  from assms have incl:
    \<open>{t::nat. t\<^sub>0 \<le> t \<and> t < t\<^sub>0+d \<and> occurs t c} \<subseteq> {t::nat. t\<^sub>0 \<le> t \<and> t < t\<^sub>0+d' \<and> occurs t c}\<close> by auto
  have \<open>card {t::nat. t\<^sub>0 \<le> t \<and> t < t\<^sub>0+d \<and> occurs t c}
        \<le> card {t::nat. t\<^sub>0 \<le> t \<and> t < t\<^sub>0+d' \<and> occurs t c}\<close>
    using card_mono[OF finite incl] .
  thus ?thesis using occurrence_count_def by simp
qed

lemma interval_diff:
  \<open>{i::nat. m \<le> i \<and> i \<le> m+l \<and> P i} = {i::nat. i \<le> m+l \<and> P i} - {i::nat. i < m \<and> P i}\<close>
by auto

corollary interval_diff_le:
  \<open>{i::nat. m+1 \<le> i \<and> i < m+1+l+1 \<and> P i} = {i::nat. i \<le> m+1+l \<and> P i} - {i::nat. i \<le> m \<and> P i}\<close>
using interval_diff[of \<open>m+1\<close> \<open>l\<close> P] Suc_eq_plus1 less_Suc_eq_le by presburger

lemma \<open>occurrence_count c (t\<^sub>0+1) (d+1) = chrono_up_to c (t\<^sub>0+d+1) - chrono_up_to c t\<^sub>0\<close>
proof -
  have 1:\<open>finite {t. t \<le> t\<^sub>0 \<and> occurs t c}\<close> by simp
  have 2:\<open>{t. t \<le> t\<^sub>0 \<and> occurs t c} \<subseteq> {t. t \<le> t\<^sub>0 + d + 1 \<and> occurs t c}\<close> by auto
  from interval_diff_le[of \<open>t\<^sub>0\<close> \<open>d\<close>] card_Diff_subset[OF 1 2] 
  show ?thesis unfolding occurrence_count_def chrono_up_to_def by simp
qed

end
