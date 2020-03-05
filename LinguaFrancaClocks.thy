theory LinguaFrancaClocks
(* Frédéric Boulanger frederic.boulanger@lri.fr, 2020 *)

imports Main

begin

section \<open>Basic definitions\<close>
text \<open>
Instants are represented as the natural numbers.
A clock represents an event that may occur or not at any instant.
We model a clock as a function from nat to bool, which is True at every
instant when the clock ticks (the event occurs). 
\<close>
type_synonym clock = \<open>nat \<Rightarrow> bool\<close>

subsection \<open>Periodic clocks\<close>
text \<open>
A clock is (k,p)-periodic if it ticks at instants separated by p instants,
starting at instant k.
\<close>
definition kp_periodic :: \<open>[nat, nat, clock] \<Rightarrow> bool\<close>
  where \<open>kp_periodic k p c \<equiv>
    (p > 0) \<and> (\<forall>n. c n = ((n \<ge> k) \<and> ((n - k) mod p = 0)))\<close>

text \<open>A 1-periodic clock always ticks starting at its offset\<close>
lemma one_periodic_ticks:
  assumes \<open>kp_periodic k 1 c\<close>
      and \<open>n \<ge> k\<close>
    shows \<open>c n\<close>
using assms kp_periodic_def by simp

text \<open>A p-periodic clock is a (k,p)-periodic clock starting from a given offset.\<close>
definition \<open>p_periodic p c \<equiv> (\<exists>k. kp_periodic k p c)\<close>

lemma p_periodic_intro[intro]:
  \<open>kp_periodic k p c \<Longrightarrow> p_periodic p c\<close>
using p_periodic_def  by blast

text \<open>No clock is 0-periodic.\<close>
lemma no_0_periodic:
  \<open>\<not>p_periodic 0 c\<close>
by (simp add: kp_periodic_def p_periodic_def)

text \<open>A periodic clock is a p-periodic clock for a given period.\<close>
definition \<open>periodic c \<equiv> (\<exists>p. p_periodic p c)\<close>

lemma periodic_intro1[intro]:
  \<open>p_periodic p c \<Longrightarrow> periodic c\<close>
using p_periodic_def periodic_def by blast

lemma periodic_intro2[intro]:
  \<open>kp_periodic k p c \<Longrightarrow> periodic c\<close>
using p_periodic_intro periodic_intro1 by blast

subsection \<open>Sporadic clocks\<close>
text \<open>
A clock is p-sporadic if it ticks at instants separated at least by p instants.
\<close>
definition p_sporadic :: \<open>[nat, clock] \<Rightarrow> bool\<close>
  where \<open>p_sporadic p c \<equiv> \<forall>t. c t \<longrightarrow> (\<forall>t'. (t' > t \<and> c t') \<longrightarrow> t' > t + p)\<close>
(*  where \<open>p_sporadic p c \<equiv> (\<forall>t. c t \<longrightarrow> (\<forall>t'. (t < t' \<and> t' \<le> t+p) \<longrightarrow> \<not>(c t')))\<close> *)

text\<open>Any clock is 0-sporadic\<close>
lemma sporadic_0: \<open>p_sporadic 0 c\<close>
  unfolding p_sporadic_def by auto

text \<open>We define sporadic clock as p-sporadic clocks for some non null interval p.\<close>
definition \<open>sporadic c \<equiv> (\<exists>p > 0. p_sporadic p c)\<close>

lemma sporadic_intro[intro]
  :\<open>\<lbrakk>p_sporadic p c;p > 0\<rbrakk> \<Longrightarrow> sporadic c\<close>
using sporadic_def by blast

section \<open>Properties of clocks\<close>

text \<open>Some useful lemmas about modulo.\<close>
lemma mod_sporadic:
  assumes \<open>((n::nat) mod p = 0)\<close>
    shows \<open>\<forall>n'. (n < n' \<and> n' < n+p) \<longrightarrow> \<not>(n' mod p = 0)\<close>
using assms less_imp_add_positive by fastforce

lemma mod_sporadic':
  assumes \<open>((n::nat) mod p = 0)\<close>
    shows \<open>\<forall>n'. (n < n' \<and> (n' mod p = 0)) \<longrightarrow> n' \<ge> n+p\<close>
proof -
  { fix n' assume h:\<open>n < n' \<and> n' mod p = 0\<close>
    hence \<open>n' \<ge> n+p\<close> using mod_sporadic[OF assms] by auto
  } thus ?thesis by simp
qed

lemma mod_offset_sporadic:
  assumes \<open>(n::nat) \<ge> k\<close>
      and \<open>(n - k) mod p = 0\<close>
    shows \<open>\<forall>n'. (n < n' \<and> n' < n+p) \<longrightarrow> \<not>((n'-k) mod p = 0)\<close>
proof -
  from assms have \<open>\<forall>n'. n' > n \<longrightarrow> (n'-k) > (n-k)\<close> by (simp add: diff_less_mono)
  with mod_sporadic[OF assms(2)] show ?thesis by auto
qed

lemma mod_offset_sporadic':
  assumes \<open>(n::nat) \<ge> k\<close>
      and \<open>(n - k) mod p = 0\<close>
    shows \<open>\<forall>n'. (n < n' \<and> ((n'-k) mod p = 0)) \<longrightarrow> n' \<ge> n+p\<close>
proof -
  from assms have \<open>\<forall>n'. n' > n \<longrightarrow> (n'-k) > (n-k)\<close> by (simp add: diff_less_mono)
  with mod_sporadic[OF assms(2)] show ?thesis by auto
qed

text \<open>A (p+1)-periodic clock is p-sporadic.\<close>
lemma periodic_suc_sporadic:
  assumes \<open>p_periodic (p+1) c\<close>
    shows \<open>p_sporadic p c\<close>
proof -
  from assms p_periodic_def obtain k
    where \<open>kp_periodic k (Suc p) c\<close> by (auto simp add: Suc_eq_plus1[symmetric])
  hence \<open>\<forall>n. c n = ((n \<ge> k) \<and> ((n - k) mod (Suc p) = 0))\<close> unfolding kp_periodic_def by simp
  thus ?thesis
    unfolding p_sporadic_def
    using mod_offset_sporadic'[where k=k and p=\<open>Suc p\<close>]
    by (simp add: Suc_le_lessD)
qed

section \<open>Merging clocks\<close>

text \<open>The result of merging two clocks ticks whenever any of the two clocks ticks.\<close>
definition merge :: \<open>[clock, clock] \<Rightarrow> clock\<close> (infix \<open>\<oplus>\<close> 60)
  where \<open>c1 \<oplus> c2 \<equiv> \<lambda>t. c1 t \<or> c2 t\<close>

lemma merge_comm: \<open>c \<oplus> c' = c' \<oplus> c\<close>
by (auto simp add: merge_def)

text \<open>Merging two sporadic clocks does not necessary yields a sporadic clock.\<close>
lemma merge_no_sporadic:
  \<open>\<exists>c c'. sporadic c \<and> sporadic c' \<and> \<not>sporadic (c\<oplus>c')\<close>
proof -
  define c :: clock where \<open>c = (\<lambda>t. t mod 2 = 0)\<close>
  define c' :: clock where \<open>c' = (\<lambda>t. t \<ge> 1 \<and> (t-1) mod 2 = 0)\<close>

  have \<open>p_periodic 2 c\<close> unfolding p_periodic_def kp_periodic_def
                        using c_def by auto
  hence 1:\<open>sporadic c\<close>
    using periodic_suc_sporadic Suc_1[symmetric] sporadic_def zero_less_one
    by auto

  have \<open>p_periodic 2 c'\<close> unfolding p_periodic_def kp_periodic_def using c'_def
    by auto
  hence 2:\<open>sporadic c'\<close>
    using periodic_suc_sporadic Suc_1[symmetric] sporadic_def zero_less_one
    by auto

  have \<open>\<not>sporadic (c\<oplus>c')\<close>
  proof -
    { assume \<open>sporadic (c \<oplus> c')\<close>
      from this obtain p where *:\<open>p > 0\<close> and \<open>p_sporadic p (c \<oplus> c')\<close>
        using sporadic_def by blast
      hence \<open>\<forall>t. (c\<oplus>c') t \<longrightarrow> (\<forall>t'. (t < t' \<and> (c\<oplus>c')t') \<longrightarrow>  t' > t+p)\<close>
        by (simp add:p_sporadic_def)
      moreover have \<open>(c\<oplus>c') 0\<close> using c_def c'_def merge_def by simp
      moreover have \<open>(c\<oplus>c') 1\<close> using c_def c'_def merge_def by simp
      ultimately have False using * by blast
    } thus ?thesis ..
  qed
  with 1 and 2 show ?thesis by blast
qed

text \<open>Get the number of ticks on a clock from the beginning up to instant n.\<close>
definition ticks_up_to :: \<open>[clock, nat] \<Rightarrow> nat\<close>
  where \<open>ticks_up_to c n = card {t. t \<le> n \<and> c t}\<close>

text \<open>There cannot be more than n event occurrences during n instants.\<close>
lemma \<open>ticks_up_to c n \<le> Suc n\<close>
proof -
  have finite: \<open>finite {t::nat. t \<le> n}\<close> by simp
  have incl: \<open>{t::nat. t \<le> n \<and> c t} \<subseteq> {t::nat. t \<le> n}\<close> by blast
  have \<open>card {t::nat. t \<le> n} = Suc n\<close> by simp
  with card_mono[OF finite incl] show ?thesis unfolding ticks_up_to_def by simp
qed

text \<open>Counting event occurrences.\<close>
definition \<open>count b n \<equiv> if b then Suc n else n\<close>

text \<open>The count of event occurrences cannot grow by more than one at each instant.\<close>
lemma count_inc: \<open>count b n \<le> Suc n\<close>
  using count_def by simp

text \<open>Alternative definition of the number of event occurrences using fold.\<close>
definition ticks_up_to_fold :: \<open>[clock, nat] \<Rightarrow> nat\<close>
  where \<open>ticks_up_to_fold c n = fold count (map c [0..<Suc n]) 0\<close>

text \<open>Alternative definition of the number of event occurrences as a function.\<close>
fun ticks_up_to_fun :: \<open>[clock, nat] \<Rightarrow> nat\<close>
where
  \<open>ticks_up_to_fun c 0 = count (c 0) 0\<close>
| \<open>ticks_up_to_fun c (Suc n) = count (c (Suc n)) (ticks_up_to_fun c n)\<close>

text \<open>
Proof that the original definition and the function definition are equivalent.
Use this to generate code.
\<close>
lemma ticks_up_to_is_fun[code]: \<open>ticks_up_to c n = ticks_up_to_fun c n\<close>
proof (induction n)
  case 0
    have \<open>ticks_up_to c 0 = card {t. t \<le> 0 \<and> c t}\<close>
      by (simp add:ticks_up_to_def)
    also have \<open>... = card {t. t=0 \<and> c t}\<close> by simp
    also have \<open>... = (if c 0 then 1 else 0)\<close>
      by (simp add: Collect_conv_if)
    also have \<open>... = ticks_up_to_fun c 0\<close>
      using ticks_up_to_fun.simps(1) count_def by simp
    finally show ?case .
next
  case (Suc n)
    show ?case
    proof (cases \<open>c (Suc n)\<close>)
      case True
        hence \<open>{t. t \<le> Suc n \<and> c t} = insert (Suc n) {t. t \<le> n \<and> c t}\<close> by auto
        hence \<open>ticks_up_to c (Suc n) = Suc (ticks_up_to c n)\<close>
          by (simp add: ticks_up_to_def)
        also have \<open>... = Suc (ticks_up_to_fun c n)\<close> using Suc.IH by simp
        finally show ?thesis by (simp add: count_def \<open>c (Suc n)\<close>)
    next
      case False
        hence \<open>{t. t \<le> Suc n \<and> c t} = {t. t \<le> n \<and> c t}\<close> using le_Suc_eq by blast
        hence \<open>ticks_up_to c (Suc n) = ticks_up_to c n\<close>
          by (simp add: ticks_up_to_def)
        also have \<open>... = ticks_up_to_fun c n\<close> using Suc.IH by simp
        finally show ?thesis by (simp add: count_def \<open>\<not>c (Suc n)\<close>)
    qed
qed

text \<open>Number of event occurrences during an n instant window starting at @{term\<open>t\<^sub>0\<close>}.\<close>
definition tick_count ::\<open>[clock, nat, nat] \<Rightarrow> nat\<close>
  where \<open>tick_count c t\<^sub>0 n \<equiv> card {t. t\<^sub>0 \<le> t \<and> t < t\<^sub>0+n \<and> c t}\<close>

text \<open>The number of event occurrences is monotonous with regard to the window width.\<close>
lemma tick_count_mono:
  assumes \<open>n' \<ge> n\<close>
    shows \<open>tick_count c t\<^sub>0 n' \<ge> tick_count c t\<^sub>0 n\<close>
proof -
  have finite: \<open>finite {t::nat. t\<^sub>0 \<le> t \<and> t < t\<^sub>0+n' \<and> c t}\<close> by simp
  from assms have incl:
    \<open>{t::nat. t\<^sub>0 \<le> t \<and> t < t\<^sub>0+n \<and> c t} \<subseteq> {t::nat. t\<^sub>0 \<le> t \<and> t < t\<^sub>0+n' \<and> c t}\<close> by auto
  have \<open>card {t::nat. t\<^sub>0 \<le> t \<and> t < t\<^sub>0+n \<and> c t}
        \<le> card {t::nat. t\<^sub>0 \<le> t \<and> t < t\<^sub>0+n' \<and> c t}\<close>
    using card_mono[OF finite incl] .
  thus ?thesis using tick_count_def by simp
qed

text \<open>The interval [t, t+n[ contains n instants.\<close>
lemma card_interval:\<open>card {t. t\<^sub>0 \<le> t \<and> t < t\<^sub>0+n} = n\<close>
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have \<open>{t. t\<^sub>0 \<le> t \<and> t < t\<^sub>0+(Suc n)} = insert (t\<^sub>0+n) {t. t\<^sub>0 \<le> t \<and> t < t\<^sub>0+n}\<close> by auto
  hence \<open>card {t. t\<^sub>0 \<le> t \<and> t < t\<^sub>0+(Suc n)} = Suc (card {t. t\<^sub>0 \<le> t \<and> t < t\<^sub>0+n})\<close> by simp
  with Suc.IH show ?case by simp
qed

text \<open>There cannot be more than n occurrences of an event in an interval of n instants.\<close>
lemma tick_count_bound: \<open>tick_count c t\<^sub>0 n \<le> n\<close>
proof -
  have finite: \<open>finite {t. t\<^sub>0 \<le> t \<and> t < t\<^sub>0+n}\<close> by simp
  have incl: \<open>{t. t\<^sub>0 \<le> t \<and> t < t\<^sub>0+n \<and> c t} \<subseteq> {t. t\<^sub>0 \<le> t \<and> t < t\<^sub>0+n}\<close> by blast
  show ?thesis using tick_count_def card_interval card_mono[OF finite incl] by simp
qed

text \<open>No event occurrence occur in 0 instant.\<close>
lemma tick_count_0[code]: \<open>tick_count c t\<^sub>0 0 = 0\<close>
  unfolding tick_count_def by simp

text \<open>Event occurrences starting from instant 0 are event occurrences from the beginning.\<close>
lemma tick_count_orig[code]:
  \<open>tick_count c 0 (Suc n) = ticks_up_to c n\<close>
unfolding tick_count_def ticks_up_to_def
using less_Suc_eq_le by simp

text \<open>
Counting event occurrences between two instants is simply subtracting
occurrence counts from the beginning.
\<close>
lemma tick_count_diff[code]:
  \<open>tick_count c (Suc t\<^sub>0) n = (ticks_up_to c (t\<^sub>0+n)) - (ticks_up_to c t\<^sub>0)\<close>
proof -
  have incl: \<open>{t. t \<le> t\<^sub>0 \<and> c t} \<subseteq> {t. t \<le> t\<^sub>0+n \<and> c t}\<close> by auto
  have \<open>{t. (Suc t\<^sub>0) \<le> t \<and> t < (Suc t\<^sub>0)+n \<and> c t}
      = {t. t \<le> t\<^sub>0+n \<and> c t} - {t. t \<le> t\<^sub>0 \<and> c t}\<close> by auto
  hence \<open>card {t. (Suc t\<^sub>0) \<le> t \<and> t < (Suc t\<^sub>0)+n \<and> c t}
       = card {t. t \<le> t\<^sub>0+n \<and> c t} - card {t. t \<le> t\<^sub>0 \<and> c t}\<close>
    by (simp add: card_Diff_subset incl)
  thus ?thesis unfolding tick_count_def ticks_up_to_def .
qed

text \<open>The merge of two clocks has less ticks than the union of the ticks of the two clocks.\<close>
lemma tick_count_merge:
  \<open>tick_count (c\<oplus>c') t\<^sub>0 n  \<le> tick_count c t\<^sub>0 n + tick_count c' t\<^sub>0 n\<close>
proof -
  have \<open>{t::nat. t\<^sub>0 \<le> t \<and> t < t\<^sub>0+n \<and> ((c\<oplus>c') t)}
        = {t::nat. t\<^sub>0 \<le> t \<and> t < t\<^sub>0+n \<and> c t} \<union> {t::nat. t\<^sub>0 \<le> t \<and> t < t\<^sub>0+n \<and> c' t}\<close>
    using merge_def by auto
  hence \<open>card {t::nat. t\<^sub>0 \<le> t \<and> t < t\<^sub>0+n \<and> ((c\<oplus>c') t)}
          \<le> card {t::nat. t\<^sub>0 \<le> t \<and> t < t\<^sub>0+n \<and> c t}
            + card {t::nat. t\<^sub>0 \<le> t \<and> t < t\<^sub>0+n \<and> c' t}\<close>  by (simp add: card_Un_le)
  thus ?thesis unfolding tick_count_def .
qed

section \<open>Bounded clocks\<close>
text \<open>An (n,m)-bounded clock does not tick more than m times in a n interval of width n.\<close>
definition bounded :: \<open>[nat, nat, clock] \<Rightarrow> bool\<close>
  where \<open>bounded n m c \<equiv> \<forall>t. tick_count c t n \<le> m\<close>

text \<open>All clocks are (n,n)-bounded.\<close>
lemma bounded_n: \<open>bounded n n c\<close>
  unfolding bounded_def using tick_count_bound by (simp add: le_imp_less_Suc)

text \<open>A sporadic clock is bounded.\<close>
lemma spor_bound:
  assumes \<open>\<forall>t::nat. c t \<longrightarrow> (\<forall>t'. (t < t' \<and> t' \<le> t+n) \<longrightarrow> \<not>(c t'))\<close>
  shows \<open>\<forall>t::nat. card {t'. t \<le> t' \<and> t' \<le> t+n \<and> c t'} \<le> 1\<close>
proof -
  { fix t::nat
    have \<open>card {t'. t \<le> t' \<and> t' \<le> t+n \<and> c t'} \<le> 1\<close>
    proof (cases \<open>c t\<close>)
      case True
        with assms have \<open>\<forall>t'. (t < t' \<and> t' \<le> t+n) \<longrightarrow> \<not>(c t')\<close> by simp
        hence empty: \<open>card {t'. t < t' \<and> t' \<le> t+n \<and> c t'} = 0\<close> by simp
        have finite: \<open>finite {t'. t < t' \<and> t' \<le> t+n \<and> c t'}\<close> by simp
        have notin: \<open>t \<notin> {t'. t < t' \<and> t' \<le> t+n \<and> c t'}\<close> by simp
        have \<open>{t'. t \<le> t' \<and> t' \<le> t+n \<and> c t'}
            = insert t {t'. t < t' \<and> t' \<le> t+n \<and> c t'}\<close> using \<open>c t\<close> by auto
        hence \<open>card {t'. t \<le> t' \<and> t' \<le> t+n \<and> c t'} = 1\<close>
          using empty card_insert_disjoint[OF finite notin] by simp
        then show ?thesis by simp
    next
      case False
      then show ?thesis
      proof(cases \<open>\<exists>tt. t < tt \<and> tt \<le> t+n \<and> c tt\<close>)
        case True
        (* Among the instants at which c ticks, there is an earliest one.*)
        hence \<open>\<exists>ttmin. t < ttmin \<and> ttmin \<le> t+n \<and> c ttmin
              \<and> (\<forall>tt'. (t < tt' \<and> tt' \<le> t+n \<and> c tt') \<longrightarrow> ttmin \<le> tt')\<close>
          by (metis add_lessD1 add_less_mono1 assms le_eq_less_or_eq
              le_refl less_imp_le_nat nat_le_iff_add nat_le_linear)
        from this obtain ttmin where
          tmin: \<open>t < ttmin \<and> ttmin \<le> t+n \<and> c ttmin
                \<and> (\<forall>tt'. (t < tt' \<and> tt' \<le> t+n \<and> c tt') \<longrightarrow> ttmin \<le> tt')\<close> by blast
        hence tick:\<open>c ttmin\<close> by simp
        with assms have notick:\<open>(\<forall>t'. ttmin < t' \<and> t' \<le> ttmin + n \<longrightarrow> \<not> c t')\<close> by simp
        have \<open>\<forall>t'. (t < t' \<and> t' < ttmin) \<longrightarrow> \<not>c t'\<close> using tmin \<open>\<not>c t\<close> by auto
        moreover from notick tmin have
          \<open>\<forall>t'. (ttmin < t' \<and> t' \<le> t+n) \<longrightarrow> \<not>c t'\<close> by auto
        ultimately have \<open>\<forall>t'::nat. (t \<le> t' \<and> t' \<le> t+n \<and> c t') \<longrightarrow> t' = ttmin\<close>
          using tick tmin \<open>\<not>c t\<close> le_eq_less_or_eq by auto
        hence \<open>{t'. t \<le> t' \<and> t' \<le> t+n \<and> c t'} = {ttmin}\<close> using tmin by fastforce
        hence \<open>card {t'. t \<le> t' \<and> t' \<le> t+n \<and> c t'} = 1\<close> by simp
        thus ?thesis by simp
      next
        case False
          with \<open>\<not>c t\<close> have \<open>\<forall>t'. t \<le> t' \<and> t' \<le> t+n \<longrightarrow> \<not>c t'\<close> 
            using nat_less_le by blast
          hence \<open>card {t'. t \<le> t' \<and> t' \<le> t+n \<and> c t'} = 0\<close> by simp
          thus ?thesis by linarith
      qed
    qed
  } thus ?thesis ..
qed

text \<open>A sporadic clock is bounded.\<close>
lemma spor_bound':
  assumes \<open>\<forall>t::nat. c t \<longrightarrow> (\<forall>t'. (t < t' \<and> c t') \<longrightarrow> t' > t+n)\<close>
  shows \<open>\<forall>t::nat. card {t'. t \<le> t' \<and> t' \<le> t+n \<and> c t'} \<le> 1\<close>
proof -
  { fix t::nat
    have \<open>card {t'. t \<le> t' \<and> t' \<le> t+n \<and> c t'} \<le> 1\<close>
    proof (cases \<open>c t\<close>)
      case True
        with assms have \<open>\<forall>t'. (t < t' \<and> c t') \<longrightarrow> t' > t+n\<close> by simp
        hence empty: \<open>card {t'. t < t' \<and> t' \<le> t+n \<and> c t'} = 0\<close> by auto
        have finite: \<open>finite {t'. t < t' \<and> t' \<le> t+n \<and> c t'}\<close> by simp
        have notin: \<open>t \<notin> {t'. t < t' \<and> t' \<le> t+n \<and> c t'}\<close> by simp
        have \<open>{t'. t \<le> t' \<and> t' \<le> t+n \<and> c t'}
            = insert t {t'. t < t' \<and> t' \<le> t+n \<and> c t'}\<close> using \<open>c t\<close> by auto
        hence \<open>card {t'. t \<le> t' \<and> t' \<le> t+n \<and> c t'} = 1\<close>
          using empty card_insert_disjoint[OF finite notin] by simp
        then show ?thesis by simp
    next
      case False
      then show ?thesis
      proof(cases \<open>\<exists>tt. t < tt \<and> tt \<le> t+n \<and> c tt\<close>)
        case True
        (* Among the instants at which c ticks, there is an earliest one.*)
        hence \<open>\<exists>ttmin. t < ttmin \<and> ttmin \<le> t+n \<and> c ttmin
              \<and> (\<forall>tt'. (t < tt' \<and> tt' \<le> t+n \<and> c tt') \<longrightarrow> ttmin \<le> tt')\<close>
          by (metis add_lessD1 add_less_mono1 assms le_Suc_ex le_eq_less_or_eq le_refl less_imp_le_nat nat_le_linear nat_neq_iff)
        from this obtain ttmin where
          tmin: \<open>t < ttmin \<and> ttmin \<le> t+n \<and> c ttmin
                \<and> (\<forall>tt'. (t < tt' \<and> tt' \<le> t+n \<and> c tt') \<longrightarrow> ttmin \<le> tt')\<close> by blast
        hence tick:\<open>c ttmin\<close> by simp
        with assms have notick:\<open>(\<forall>t'. ttmin < t' \<and> c t' \<longrightarrow> t' > ttmin + n)\<close> by simp
        have \<open>\<forall>t'. (t < t' \<and> t' < ttmin) \<longrightarrow> \<not>c t'\<close> using tmin \<open>\<not>c t\<close> by auto
        moreover from notick tmin have
          \<open>\<forall>t'. (ttmin < t' \<and> t' \<le> t+n) \<longrightarrow> \<not>c t'\<close> by auto
        ultimately have \<open>\<forall>t'::nat. (t \<le> t' \<and> t' \<le> t+n \<and> c t') \<longrightarrow> t' = ttmin\<close>
          using tick tmin \<open>\<not>c t\<close> le_eq_less_or_eq by auto
        hence \<open>{t'. t \<le> t' \<and> t' \<le> t+n \<and> c t'} = {ttmin}\<close> using tmin by fastforce
        hence \<open>card {t'. t \<le> t' \<and> t' \<le> t+n \<and> c t'} = 1\<close> by simp
        thus ?thesis by simp
      next
        case False
          with \<open>\<not>c t\<close> have \<open>\<forall>t'. t \<le> t' \<and> t' \<le> t+n \<longrightarrow> \<not>c t'\<close> 
            using nat_less_le by blast
          hence \<open>card {t'. t \<le> t' \<and> t' \<le> t+n \<and> c t'} = 0\<close> by simp
          thus ?thesis by linarith
      qed
    qed
  } thus ?thesis ..
qed

text \<open>An n-sporadic clock is (n+1, 1)-bounded.\<close>
lemma spor_bounded:
  assumes \<open>p_sporadic n c\<close>
    shows \<open>bounded (n+1) 1 c\<close>
proof -
  from assms have \<open>\<forall>t. c t \<longrightarrow> (\<forall>t'. (t < t' \<and> c t') \<longrightarrow> t' > t+n)\<close>
    using p_sporadic_def by simp
  from spor_bound'[OF this] have \<open>\<forall>t. card {t'. t \<le> t' \<and> t' \<le> t+n \<and> c t'} \<le> 1\<close> .
  hence \<open>\<forall>t. card {t'. t \<le> t' \<and> t' < Suc (t+n) \<and> c t'} \<le> 1\<close>
    using less_Suc_eq_le by auto
  hence \<open>\<forall>t. card {t'. t \<le> t' \<and> t' < t + Suc n \<and> c t'} \<le> 1\<close> by auto
  thus ?thesis unfolding bounded_def tick_count_def Suc_eq_plus1 .
qed

text \<open>An n-sporadic clock is (n+2, 2)-bounded.\<close>
lemma spor_bounded2:
  assumes \<open>p_sporadic n c\<close>
    shows \<open>bounded (n+2) 2 c\<close>
proof -
  from spor_bounded[OF assms] have
      *:\<open>\<forall>t. card {t'. t \<le> t' \<and> t' < t + Suc n \<and> c t'} \<le> 1\<close>
    unfolding bounded_def tick_count_def by simp
  hence \<open>\<forall>t. card {t'. t \<le> t' \<and> t' < Suc (t + Suc n) \<and> c t'} \<le> Suc 1\<close>
  proof -
    { fix t::nat
      from * have **:\<open>card {t'. t \<le> t' \<and> t' < t + Suc n \<and> c t'} \<le> 1\<close> by simp
      have \<open>card {t'. t \<le> t' \<and> t' < Suc (t + Suc n) \<and> c t'} \<le> Suc 1\<close>
      proof (cases \<open>c (t + Suc n)\<close>)
        case True
          hence \<open>{t'. t \<le> t' \<and> t' < Suc (t + Suc n) \<and> c t'}
                = insert (t+Suc n) {t'. t \<le> t' \<and> t' < t + Suc n \<and> c t'}\<close> by auto
          hence \<open>card {t'. t \<le> t' \<and> t' < Suc (t + Suc n) \<and> c t'}
                = Suc (card {t'. t \<le> t' \<and> t' < t + Suc n \<and> c t'})\<close> by simp
          thus ?thesis using ** by simp 
      next
        case False
          hence \<open>{t'. t \<le> t' \<and> t' < Suc (t + Suc n) \<and> c t'}
                = {t'. t \<le> t' \<and> t' < t + Suc n \<and> c t'}\<close> using less_Suc_eq by blast
          hence \<open>card {t'. t \<le> t' \<and> t' < Suc (t + Suc n) \<and> c t'}
                  = (card {t'. t \<le> t' \<and> t' < t + Suc n \<and> c t'})\<close> by simp
          thus ?thesis using ** by simp 
      qed
    } thus ?thesis ..
  qed
  thus ?thesis unfolding bounded_def tick_count_def
    by (metis Suc_1 add_Suc_right Suc_eq_plus1)
qed

text \<open>A bounded clock on an interval is also bounded on a narrower interval.\<close>
lemma bounded_less:
  assumes \<open>bounded n' m c\<close>
      and \<open>n' \<ge> n\<close>
    shows \<open>bounded n m c\<close>
  using assms(1) unfolding bounded_def
  using tick_count_mono[OF assms(2)] order_trans by blast

text \<open>The merge of two bounded clocks is bounded.\<close>
lemma bounded_merge:
  assumes \<open>bounded n m c\<close>
      and \<open>bounded n' m' c'\<close>
      and \<open>n' \<ge> n\<close>
    shows \<open>bounded n (m+m') (c\<oplus>c')\<close>
using tick_count_merge bounded_less[OF assms(2,3)] assms(1,2) add_mono order_trans
  unfolding bounded_def by blast

text \<open>The merge of two sporadic clocks is bounded.\<close>
lemma sporadic_bounded1:
  assumes \<open>p_sporadic n c\<close>
      and \<open>p_sporadic n' c'\<close>
      and \<open>n' \<ge> n\<close>
    shows \<open>bounded (n+1) 2 (c\<oplus>c')\<close>
proof -
  have 1:\<open>bounded (n+1) 1 c\<close> using spor_bounded[OF assms(1)] .
  have 2:\<open>bounded (n'+1) 1 c'\<close> using spor_bounded[OF assms(2)] .
  from assms(3) have 3:\<open>n'+1 \<ge> n+1\<close> by simp
  have \<open>1+1 = (2::nat)\<close> by simp
  with bounded_merge[OF 1 2 3] show ?thesis by metis
qed

subsection \<open>Main theorem\<close>
text \<open>The merge of two sporadic clocks is bounded on the min of the bounding intervals.\<close>
theorem sporadic_bounded_min:
  assumes \<open>p_sporadic n c\<close>
      and \<open>p_sporadic n' c'\<close>
    shows \<open>bounded ((min n n')+1) 2 (c\<oplus>c')\<close>
proof (cases \<open>n \<le> n'\<close>)
  case True
    hence \<open>min n n' = n\<close> by simp
    thus ?thesis using sporadic_bounded1[OF assms True] by simp
next
  case False
    hence 1:\<open>n' = min n n'\<close> and 2:\<open>n' \<le> n\<close> by simp+
    from sporadic_bounded1[OF assms(2) assms(1) 2] 1 show ?thesis using merge_comm  by simp
  qed

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
