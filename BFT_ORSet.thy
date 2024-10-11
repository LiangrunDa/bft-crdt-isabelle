(* Liangrun Da, Technical University of Munich
   Martin Kleppmann, University of Cambridge
*)
theory BFT_ORSet
  imports BFT_Convergence
begin

section \<open>BFT ORSet\<close>

text \<open>
  Our definition is based on the non-BFT ORSet Isabelle definition of an operation-based ORSet 
  shown in~\cite{CRDT-AFP}. Unlike the traditional ORSet, our BFT version does not include an element 
  id in the $\isa{Add}$ operation. This modification is necessary because allowing the operation's 
  creator to choose the ID would enable attackers to create multiple operations with the same value 
  and ID but different predecessors, thus compromising the uniqueness of the ID.
\<close>

subsection \<open>Definition\<close>

datatype ('id, 'a) operation = Add \<open>'a\<close> | Rem \<open>'id set\<close> \<open>'a\<close>
type_synonym ('id, 'a) state = \<open>'a \<Rightarrow> 'id set\<close>
type_synonym ('hash, 'a) ORSetG = \<open>('hash, ('hash, 'a) operation) hash_graph\<close>
type_synonym ('hash, 'a) ORSetN = \<open>('hash, ('hash, 'a) operation) node\<close>
type_synonym ('hash, 'a) ORSetH = \<open>('hash, ('hash, 'a) operation) hash_func\<close>
type_synonym ('hash, 'a) ORSetC = \<open>('hash, ('hash, 'a) operation) causal_func\<close>

definition op_elem :: \<open>('id, 'a) operation \<Rightarrow> 'a\<close> where
  \<open>op_elem oper \<equiv> case oper of Add e \<Rightarrow> e | Rem is e \<Rightarrow> e\<close>

text \<open>When interpreting an $\isa{Add}$ operation, we generate a unique ID for the element by hashing 
  the node that contains the $\isa{Add}$ operation.\<close>

fun interpret_op' :: \<open>('hash, 'a) ORSetH  \<Rightarrow> ('hash, 'a) ORSetN \<Rightarrow> ('hash, 'a) state \<Rightarrow> ('hash, 'a) state option\<close> where
  \<open>interpret_op' H (hs, oper) state = (
     let before = state (op_elem oper);
         after  = case oper of 
            Add e \<Rightarrow> before \<union> {H (hs, oper)} 
          | Rem is e \<Rightarrow> before - is
     in  Some (state ((op_elem oper) := after)))\<close>

text \<open>
  An Add operation is always semantically valid and can always be added to the hash graph. A Rem 
  operation is only valid if all the IDs it intends to remove are already present in its ancestors. 
  This ensures that we only remove elements that have been previously added. Here $\isa{C}$ is a 
  placeholder for a $\isa{ancestor}$ relation, which is not defined before instantiating the locale. 
  $\isa{C n (hs, Rem is e)}$ means the $n$ is an ancestor of the node that contains the $\isa{Rem}$ 
  operation.
\<close>

fun is_orset_sem_valid :: \<open>('hash, 'a) ORSetC \<Rightarrow> ('hash, 'a) ORSetH \<Rightarrow> ('hash, 'a) ORSetN set \<Rightarrow> ('hash, 'a) ORSetN \<Rightarrow> bool\<close> where
  \<open>is_orset_sem_valid C H S (hs, Add e) = True\<close>
| \<open>is_orset_sem_valid C H S (hs, Rem is e) = 
    (\<forall>i \<in> is. \<exists> n \<in> S. (C n (hs, Rem is e)) \<and> (snd n = Add e) \<and> (H n = i))\<close>

locale bft_orset = peers_with_arbitrary_history H _ interpret_op' \<open>\<lambda>x. {}\<close> is_orset_sem_valid for
    H :: \<open>('hash, 'a) ORSetH\<close>
begin

notation interp (\<open>\<langle>_\<rangle>\<close> [0] 1000)

subsection \<open>No Failure\<close>

lemma interpret_op'_never_fails: \<open>interpret_op' H n S \<noteq> None\<close>
  apply (clarsimp split: operation.splits)
  by (meson interpret_op'.elims)

lemma step_never_fails:
  assumes \<open>apply_history ([], {||}) ns = (dn, G)\<close>
     and \<open>no_failure dn\<close>
     and \<open>check_and_apply (dn, G) (hs, v) = (dn', G')\<close>
   shows \<open>no_failure dn'\<close>
using assms proof (cases "is_valid G (hs, v)")
  case True
  then show ?thesis using interpret_op'_never_fails apply_operations_def apply_operations_snoc 
      assms(2) assms(3) no_failure_def by auto
next
  case False
  then show ?thesis
    by (metis assms(2) assms(3) check_and_apply.simps fst_eqD)
qed
                                                              
subsection \<open>Concurrent Operations Commute\<close>

lemma rem_has_ancestor_ids:
  assumes \<open>valid_graph G\<close>
    and \<open>x = (hs, Rem is e)\<close>
    and \<open>x |\<in>| G\<close>
  shows \<open>\<forall>i \<in> is. \<exists>n |\<in>| G. snd n = Add e \<and> H n = i\<close>
using assms proof(induction arbitrary: x rule: valid_graph.induct)
  case 1
  then show ?case
    by blast
next
  case (2 G n)
  then show ?case 
    by fastforce
qed

lemma sem_valid_concurrent:
  assumes \<open>valid_graph G\<close>
    and \<open>x = (hs1, (Add e1))\<close>
    and \<open>y = (hs2, (Rem is e2))\<close>
    and \<open>x |\<in>| G\<close>
    and \<open>y |\<in>| G\<close>
    and \<open>hb.concurrent x y\<close>
  shows \<open>H (hs1, (Add e1)) \<notin> is\<close>
using assms proof(induction arbitrary: x y rule: valid_graph.induct)
  case 1
  then show ?case 
    by auto
next
  case (2 G n)
  then show ?case proof (cases \<open>snd n\<close>)
    case (Add x1)
    then show ?thesis 
      apply (cases \<open>x |\<in>| G\<close>; cases \<open>y |\<in>| G\<close>)
         defer 3
      using "2.IH" "2.prems" assms apply force+
      by (metis "2.hyps"(1) "2.prems"(1) "2.prems"(2) hash_no_collisions rem_has_ancestor_ids)
  next
  next
    case (Rem x21 x22)
    then show ?thesis 
      apply (cases \<open>x |\<in>| G\<close>; cases \<open>y |\<in>| G\<close>)
         defer 2
      using "2.IH" "2.prems" assms apply force+
      using "2.hyps"(2) "2.prems"(2) "2.prems"(4) assms(2) assms(3) assms(6) 
        hash_no_collisions hb.concurrent_def by fastforce
  qed
qed

lemma add_add_commute:
  shows \<open>\<langle>(hs1, Add e1)\<rangle> \<rhd> \<langle>(hs2, Add e2)\<rangle> = \<langle>(hs2, Add e2)\<rangle> \<rhd> \<langle>(hs1, Add e1)\<rangle>\<close>
  by(auto simp add: op_elem_def kleisli_def, fastforce)

lemma add_rem_commute:
  assumes \<open>H (hs1, Add e1) \<notin> is\<close>
  shows \<open>\<langle>(hs1, Add e1)\<rangle> \<rhd> \<langle>(hs2, Rem is e2)\<rangle> = \<langle>(hs2, Rem is e2)\<rangle> \<rhd> \<langle>(hs1, Add e1)\<rangle>\<close>
  using assms by(auto simp add: kleisli_def op_elem_def, fastforce)

lemma rem_rem_commute:
  shows \<open>\<langle>(hs1, Rem i1 e1)\<rangle> \<rhd> \<langle>(hs2, Rem i2 e2)\<rangle> = \<langle>(hs2, Rem i2 e2)\<rangle> \<rhd> \<langle>(hs1, Rem i1 e1)\<rangle>\<close>
  by(unfold op_elem_def kleisli_def, fastforce)

lemma concurrent_add_remove_independent:
  assumes \<open>valid_graph G\<close>
    and \<open>(hs1, Add e1) \<parallel> (hs2, Rem is e2)\<close>
    and \<open>(hs1, Add e1) |\<in>| G\<close> and \<open>(hs2, Rem is e2) |\<in>| G\<close>
  shows \<open>H (hs1, Add e1) \<notin> is\<close>
  by (meson assms(1) assms(2) assms(3) assms(4) hb.concurrentI is_concurrent_def sem_valid_concurrent)

lemma concurrent_operations_commute:
  assumes \<open>xs = (delivered_nodes i)\<close>
  shows \<open>hb.concurrent_ops_commute xs\<close>  
proof -       
  { fix hs1 hs2 op1 op2
    assume a1: \<open>(hs1, op1) \<in> set xs\<close>
           and a2: \<open>(hs2, op2) \<in> set xs\<close>
           and a3: \<open>hb.concurrent (hs1, op1) (hs2, op2)\<close>
    have 1: \<open>(hs1, op1) |\<in>| (graph i)\<close>
      using a1 assms in_history_in_graph by blast
    have 2: \<open>(hs2, op2) |\<in>| (graph i)\<close>
      using a2 assms in_history_in_graph by blast
    have 3: \<open>valid_graph (graph i)\<close>
      by (metis apply_history_preserve_validity local.graph_def peer_state.simps prod.collapse valid_graph.intros(1))
    then have \<open>\<langle>(hs1, op1)\<rangle> \<rhd> \<langle>(hs2, op2)\<rangle> =
            \<langle>(hs2, op2)\<rangle> \<rhd> \<langle>(hs1, op1)\<rangle>\<close> 
      apply (case_tac \<open>op1\<close>; case_tac \<open>op2\<close>)
         apply (meson add_add_commute)
      using 1 2 a3 add_rem_commute sem_valid_concurrent apply auto[1]
      using 1 2 a3 add_rem_commute hb.concurrent_comm sem_valid_concurrent apply auto[1]
      by (meson rem_rem_commute)
  } thus ?thesis
    by(fastforce simp: hb.concurrent_ops_commute_def)
qed

subsection \<open>Synchronization\<close>

lemma sem_valid_only_ancestors_relevant: 
  assumes \<open>(ancestor_nodes_of n) \<subseteq> fset G\<close>
  shows \<open>is_sem_valid_set (ancestor_nodes_of n) n \<longleftrightarrow> is_sem_valid G n\<close>
proof
  assume assm_v: \<open>is_sem_valid_set (ancestor_nodes_of n) n\<close>
  show \<open>is_sem_valid G n\<close> proof (cases \<open>snd n\<close>)
    case (Add x1)
    then show ?thesis 
      by (metis is_orset_sem_valid.simps(1) is_sem_valid.elims(3) prod.collapse)
  next
    case (Rem ids e)
    show ?thesis proof (rule ccontr)
      assume assm_n: \<open>\<not> is_sem_valid G n\<close>
      obtain hs where n_d: \<open>n = (hs, (Rem ids e))\<close>
        by (metis Rem surjective_pairing)
      then have \<open>\<exists>i \<in> ids. \<not>(\<exists>y. y \<in> fset G \<and> (y \<prec> (hs, (Rem ids e))) \<and> (snd y = Add e) \<and> (H y = i))\<close>
        using assm_n by force
      moreover have \<open>\<forall>i \<in> ids. (\<exists>y. y \<in> (ancestor_nodes_of n) \<and> (y \<prec> (hs, (Rem ids e))) \<and> (snd y = Add e) \<and> (H y = i))\<close>
        using assm_v n_d by force
      ultimately show \<open>False\<close>
        using assms by fastforce
    qed
  qed
next
  assume assm_v: \<open>is_sem_valid G n\<close> 
  show \<open>is_sem_valid_set (ancestor_nodes_of n) n\<close> proof (cases \<open>snd n\<close>)
    case (Add x1)
    then show ?thesis 
      by (metis is_orset_sem_valid.simps(1) is_sem_valid_set.elims(3) prod.collapse)
  next
    case (Rem ids e)
    show ?thesis proof (rule ccontr)
      assume assm_n: \<open>\<not> is_sem_valid_set (ancestor_nodes_of n) n\<close>
      obtain hs where n_d: \<open>n = (hs, (Rem ids e))\<close>
        by (metis Rem surjective_pairing)
      have \<open>\<exists>i \<in> ids. \<not>(\<exists>y. y \<in> (ancestor_nodes_of n) \<and> (y \<prec> (hs, (Rem ids e))) \<and> (snd y = Add e) \<and> (H y = i))\<close>
        using assm_n n_d by force
      moreover have \<open>\<forall>i \<in> ids. (\<exists>y. y \<in> fset G \<and> (y \<prec> (hs, (Rem ids e))) \<and> (snd y = Add e) \<and> (H y = i))\<close>
        using assm_v n_d by fastforce
      ultimately show \<open>False\<close>
        using ancestor_nodes_of_def n_d by auto
    qed
  qed
qed

sublocale sec: bft_strong_eventual_consistency H _ interpret_op' \<open>\<lambda>x. {}\<close> is_orset_sem_valid
proof 
  fix n G 
  assume \<open>ancestor_nodes_of n \<subseteq> fset G\<close>
  show \<open>is_sem_valid_set (ancestor_nodes_of n) n = is_sem_valid G n\<close> 
    using \<open>ancestor_nodes_of n \<subseteq> fset G\<close> sem_valid_only_ancestors_relevant by presburger
next
  fix i
  show \<open>hb.concurrent_ops_commute (delivered_nodes i)\<close>
    by (simp add: concurrent_operations_commute)
next
  fix ns dn G hs v dn' G'
  show \<open>apply_history ([], {||}) ns = (dn, G) \<Longrightarrow>
       no_failure dn \<Longrightarrow>
       check_and_apply (dn, G) (hs, v) = (dn', G') \<Longrightarrow> no_failure dn'\<close>
    using step_never_fails by blast
qed

end

end