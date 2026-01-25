(* Liangrun Da, Technical University of Munich
   Martin Kleppmann, University of Cambridge
*)
theory BFT_Counter
  imports BFT_Convergence
begin

datatype operation = Increment | Decrement
type_synonym state = int
type_synonym ('hash) CounterG = \<open>('hash, operation) hash_graph\<close>
type_synonym ('hash) CounterN = \<open>('hash, operation) node\<close>
type_synonym ('hash) CounterH = \<open>('hash, operation) hash_func\<close>
type_synonym ('hash) CounterC = \<open>('hash, operation) causal_func\<close>

fun counter_op :: \<open>operation \<Rightarrow> state \<rightharpoonup> state\<close> where
  \<open>counter_op Increment x = Some (x + 1)\<close> |
  \<open>counter_op Decrement x = Some (x - 1)\<close>

fun interpret_op' :: \<open>('hash) CounterH  \<Rightarrow> ('hash) CounterN \<Rightarrow> state \<Rightarrow> state option\<close> where
  \<open>interpret_op' _ (_, oper) s = counter_op oper s\<close>

fun is_counter_sem_valid :: \<open>('hash) CounterC \<Rightarrow> ('hash) CounterH \<Rightarrow> ('hash) CounterN set \<Rightarrow> ('hash) CounterN \<Rightarrow> bool\<close> where
  \<open>is_counter_sem_valid _ _ _ _ = True\<close>

locale bft_counter = peers_with_arbitrary_history H _ interpret_op' \<open>0\<close> is_counter_sem_valid for
    H :: \<open>('hash) CounterH\<close>
begin

notation interp (\<open>\<langle>_\<rangle>\<close> [0] 1000)


subsection \<open>No Failure\<close>

lemma interpret_op'_never_fails: \<open>interpret_op' H n S \<noteq> None\<close>
  by (metis counter_op.elims interpret_op'.elims not_Some_eq)

lemma step_never_fails:
  assumes \<open>apply_history ([], {||}) ns = (dn, G)\<close>
     and \<open>no_failure dn\<close>
     and \<open>check_and_apply (dn, G) (hs, v) = (dn', G')\<close>
   shows \<open>no_failure dn'\<close>
  by (metis apply_operations_def apply_operations_snoc initial_state_no_failure interp.simps 
      interpret_op'_never_fails no_failure_def not_None_eq rev_induct)

subsection \<open>Concurrent Operations Commute\<close>

lemma counter_op_commute: \<open>counter_op x \<rhd> counter_op y = counter_op y \<rhd> counter_op x\<close>
  by(case_tac x; case_tac y; auto simp add: kleisli_def)

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
      by (metis counter_op_commute ext interp.elims interpret_op'.simps)
  } thus ?thesis
    by(fastforce simp: hb.concurrent_ops_commute_def)
qed

subsection \<open>Synchronization\<close>

lemma sem_valid_only_ancestors_relevant: 
  assumes \<open>(ancestor_nodes_of n) \<subseteq> fset G\<close>
  shows \<open>is_sem_valid_set (ancestor_nodes_of n) n \<longleftrightarrow> is_sem_valid G n\<close>
  by auto


sublocale sec: bft_strong_eventual_consistency H _ interpret_op' \<open>0\<close> is_counter_sem_valid
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

definition is_counter_sem_valid_impl :: \<open>(String.literal) CounterC \<Rightarrow> (String.literal) CounterH \<Rightarrow> (String.literal) CounterN set \<Rightarrow> (String.literal) CounterN \<Rightarrow> bool\<close>
  where
    \<open>is_counter_sem_valid_impl = is_counter_sem_valid\<close>

definition counter_interpret_op_impl :: \<open>(String.literal) CounterH  \<Rightarrow> (String.literal) CounterN \<Rightarrow> state \<Rightarrow> state option\<close> where
  \<open>counter_interpret_op_impl = interpret_op'\<close>

definition counter_is_struct_valid_impl :: \<open>(String.literal) CounterH \<Rightarrow> (String.literal) CounterG \<Rightarrow> (String.literal) CounterN \<Rightarrow> bool\<close> where
  \<open>counter_is_struct_valid_impl = is_struct_valid'\<close>

type_synonym ('hash, 'val) impl_causal_func = \<open>('hash, 'val) hash_graph \<Rightarrow> ('hash, 'val) node \<Rightarrow>('hash, 'val) node \<Rightarrow> bool\<close>
type_synonym ('hash) impl_CounterC = \<open>('hash, operation) impl_causal_func\<close>

definition counter_check_and_apply :: \<open>(String.literal) impl_CounterC \<Rightarrow> (String.literal) CounterH \<Rightarrow> (String.literal, operation) peer_state \<Rightarrow> (String.literal, operation) node \<Rightarrow> (String.literal, operation) peer_state\<close> where
  \<open>counter_check_and_apply C H = check_and_apply' (\<lambda>G. (is_counter_sem_valid_impl (C G) H) (fset G)) (counter_is_struct_valid_impl H)\<close>


export_code is_counter_sem_valid_impl counter_interpret_op_impl counter_is_struct_valid_impl counter_check_and_apply in Scala module_name BFT_ORSet file "BFT_Counter.scala"

end