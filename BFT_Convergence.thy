(* Liangrun Da, Technical University of Munich
   Martin Kleppmann, University of Cambridge
*)
theory BFT_Convergence
  imports Hash_Graph "CRDT.Convergence"
begin

section \<open> BFT Convergence \<close>

text \<open> 
  We model the system as a network of multiple peers, where each peer has a node history. This 
  history represents a list of hash graph nodes that are either generated locally or received 
  from remote peers. We assume that correct peers discard received messages that do not conform to 
  the hash graph node format. Besides, we assume that the attacker cannot construct multiple hash 
  graph nodes such that they form a cycle. This is a reasonable assumption because, for a cryptographic 
  hash function, this is generally believed to be computationally infeasible. We place no other 
  restrictions on the history. In other words, we make no assumptions about the attacker: an attacker 
  can send any hash graph node to the victim, combine them arbitrarily, collaborate with other 
  attackers, and even control the order in which these hash graph nodes are received.

  Additionally, the model requires a function $\isa{interp'}$ that represents an abstract interpretation 
  function of a CRDT. It takes a hash graph node and transforms one state into another, similarly to 
  Gomes et al.~\cite{gomes2017verifying}'s approach. The function $\isa{is-sem-valid'}$ represents 
  the semantic validation operation of a CRDT. This means that any hash graph node in the history 
  must pass the $\isa{is-sem-valid'}$ check before being interpreted. If it does not pass the check, 
  it is discarded without being applied to the state. The definitions of $\isa{interp'}$ and 
  $\isa{is-sem-valid'}$ are different for each CRDT. The $\isa{initial-state}$, as the name suggests, 
  is the initial CRDT state of each peer, which is also determined by the specific CRDT. 
\<close>

subsection \<open>Behavior of Correct Peers\<close>

text \<open> 
  Each correct peer maintains a local state, which includes a list of delivered nodes and a hash graph. 
  The delivered nodes refers to the sequence of hash graph nodes in the peer's history that have passed 
  the structual and semantic validity checks. In practice, a peer only needs to store the hash graph, 
  while the delivered nodes is used solely for proof purposes, as any delivered node is applied 
  immidiately to the CRDT state. 
\<close>

type_synonym ('hash, 'val) peer_state = \<open>('hash, 'val) node list \<times> ('hash, 'val) hash_graph\<close>

locale peers_with_arbitrary_history = hash_graph H    
  for H :: \<open>('hash, 'val) hash_func\<close> + 
  fixes history :: \<open>nat \<Rightarrow> ('hash, 'val) node list\<close>
    and interp' :: \<open>('hash, 'val) hash_func \<Rightarrow> ('hash, 'val) node \<Rightarrow> 'state \<rightharpoonup> 'state\<close>
    and initial_state :: \<open>'state\<close>
    and is_sem_valid' :: \<open>('hash, 'val) causal_func \<Rightarrow> ('hash, 'val) hash_func \<Rightarrow> ('hash, 'val) node set \<Rightarrow> ('hash, 'val) node \<Rightarrow> bool\<close>
  assumes no_cycle: \<open>x \<prec> y \<and> y \<prec> x \<Longrightarrow> False\<close>
begin

text \<open>
  To reuse the abstract convergence theory, we instantiate the locale with ancestor relation. From this 
  point, we can reuse all the abstract results in the locale $\isa{happens-before}$.
\<close>

fun interp :: \<open>('hash, 'val) node \<Rightarrow> 'state \<rightharpoonup> 'state\<close> (\<open>\<langle>_\<rangle>\<close> [0] 1000) where
  \<open>interp n s = interp' H n s\<close>

lemma ancestor_anti_sym:
  assumes \<open>x \<prec> y\<close>
    and \<open>y \<prec> x\<close>
  shows \<open>False\<close>
  using assms(1) assms(2) peers_with_arbitrary_history_axioms 
    peers_with_arbitrary_history_axioms_def peers_with_arbitrary_history_def by blast

lemma ancestor_less_le_not_le:
  \<open>x \<prec> y = (x \<preceq> y \<and> \<not> y \<preceq> x)\<close>
proof
  fix x y
  assume \<open>x \<prec> y\<close>
  then show \<open>x \<preceq> y \<and> \<not> y \<preceq> x\<close>
    using ancestor_anti_sym reachable_def by blast
next
  fix x y
  assume \<open>x \<preceq> y \<and> \<not> y \<preceq> x\<close>
  then show \<open>x \<prec> y\<close>
    using reachable_def by auto
qed

sublocale hb: happens_before reachable ancestor interp
proof
  fix x y
  show \<open>(x \<prec> y) = (x \<preceq> y \<and> \<not> y \<preceq> x)\<close>
    by (simp add: ancestor_less_le_not_le)
next
  fix x y
  show \<open>x \<preceq> x\<close>
    by (simp add: reachable_def)
next
  fix x y z
  show \<open>x \<preceq> y \<Longrightarrow> y \<preceq> z \<Longrightarrow> x \<preceq> z\<close>
    using reachable_transitivity by blast
qed

text \<open>
  We then inductively define a predicate $\isa{sem-valid}$ that checks if a hash graph is 
  semantically valid. A hash graph is $\isa{sem-valid}$ either if it is empty or if it is extended 
  by a new hash node that is semantically valid with respect to a $\isa{sem-valid}$ hash graph.
\<close>

fun is_sem_valid :: \<open>('hash, 'val) hash_graph \<Rightarrow> ('hash, 'val) node \<Rightarrow> bool\<close> where
  \<open>is_sem_valid G n = is_sem_valid' (\<prec>) H (fset G) n\<close>

fun is_sem_valid_set :: \<open>('hash, 'val) node set \<Rightarrow> ('hash, 'val) node \<Rightarrow> bool\<close> where
  \<open>is_sem_valid_set S n = is_sem_valid' (\<prec>) H S n\<close>

definition apply_operations :: \<open>('hash, 'val) node list \<Rightarrow> 'state option\<close> where
  \<open>apply_operations ns \<equiv> hb.apply_operations ns initial_state\<close>

fun is_valid :: \<open>('hash, 'val) hash_graph \<Rightarrow> ('hash, 'val) node \<Rightarrow> bool\<close> where
  \<open>is_valid G x = ((is_sem_valid G x) \<and> (is_struct_valid G x))\<close>

inductive sem_valid :: \<open>('hash, 'val) hash_graph \<Rightarrow> bool\<close> where 
  \<open>sem_valid {||}\<close>
| \<open>\<lbrakk> sem_valid G; is_sem_valid G n\<rbrakk> \<Longrightarrow> sem_valid (G |\<union>| {|n|})\<close>

inductive_cases sem_valid_indcases: \<open>sem_valid G\<close>

inductive valid_graph :: \<open>('hash, 'val) hash_graph \<Rightarrow> bool\<close> where 
  \<open>valid_graph {||}\<close>
| \<open>\<lbrakk> valid_graph G; is_valid G n\<rbrakk> \<Longrightarrow> valid_graph (G |\<union>| {|n|})\<close>

inductive_cases valid_indcases: \<open>valid_graph G\<close>

lemma valid_graph_implies_struct_valid[intro]: \<open>valid_graph G \<Longrightarrow> struct_valid G\<close>
proof(induction rule: valid_graph.induct)
  case 1
  then show ?case 
    by (simp add: empty_graph)
next
  case (2 G n)
  then show ?case
    by (metis is_struct_valid.elims(2) is_valid.elims(2) struct_valid.simps)
qed

lemma valid_graph_implies_sem_valid[intro]: \<open>valid_graph G \<Longrightarrow> sem_valid G\<close>
proof(induction rule: valid_graph.induct)
  case 1
  then show ?case 
    using sem_valid.intros(1) by auto
next
  case (2 G n)
  then show ?case
    using sem_valid.intros(2) by auto
qed

text \<open> 
  A correct peer first checks both the semantic and structural validity of the node against the 
  local state. If the node is valid, the peer deliver the update and add it to its hash graph. 
\<close>

fun check_and_apply :: \<open>('hash, 'val) peer_state \<Rightarrow> ('hash, 'val) node \<Rightarrow> ('hash, 'val) peer_state\<close> where
  \<open>check_and_apply (ah, G) n = 
    (if is_valid G n then 
      (ah @ [n], G |\<union>| {|n|})
    else
      (ah, G)
    )
\<close>

fun apply_history :: \<open>('hash, 'val) peer_state \<Rightarrow> ('hash, 'val) node list \<Rightarrow> ('hash, 'val) peer_state\<close> where
  \<open>apply_history S ns = foldl check_and_apply S ns\<close>

fun peer_state :: \<open>nat \<Rightarrow> ('hash, 'val) peer_state\<close> where
  \<open>peer_state i = apply_history ([], {||}) (history i)\<close>

definition graph :: \<open>nat \<Rightarrow> ('hash, 'val) hash_graph\<close> where
  \<open>graph i = snd (peer_state i)\<close>

definition delivered_nodes :: \<open>nat \<Rightarrow> ('hash, 'val) node list\<close> where
  \<open>delivered_nodes i = fst (peer_state i)\<close>

definition no_failure :: \<open>('hash, 'val) node list \<Rightarrow> bool\<close> where
  \<open>no_failure xs = (hb.apply_operations xs initial_state \<noteq> None)\<close>

subsection \<open>Properties of a Correct Peer\<close>

lemma initial_state_no_failure: \<open>no_failure []\<close>
  by (simp add: no_failure_def)

lemma apply_operations_snoc[simp]:
  assumes \<open>apply_operations ns = Some s\<close>
  shows \<open>apply_operations (ns @ [n]) = interp n s\<close>
  by (metis(full_types) apply_operations_def assms bind.bind_lunit hb.apply_operations_Snoc kleisli_def)

lemma apply_operations_Some:
  assumes \<open>apply_operations (ns @ [n]) = Some s\<close>
  shows \<open>\<exists>s'. apply_operations ns = Some s'\<close>
proof (rule ccontr)
  assume "\<nexists>s'. apply_operations ns = Some s'"
  then have ns_none: \<open>apply_operations ns = None\<close>
    by simp
  have 2: \<open>apply_operations (ns @ [n]) = ((hb.apply_operations ns) \<rhd> \<langle>n\<rangle>) initial_state\<close>
    by (simp add: apply_operations_def)
  then have 1: \<open>\<dots> = ((hb.apply_operations ns) initial_state \<bind> (\<lambda>y. \<langle>n\<rangle> y))\<close>
    by (simp add: kleisli_def)
  then have \<open>\<dots> = None\<close>
    using ns_none apply_operations_def by fastforce
  then show \<open>False\<close>
    using assms "1" "2" by auto
qed

lemma apply_history_snoc[simp]:
  assumes \<open>apply_history (dn, G) xs = (dn', G')\<close>
  shows \<open>apply_history (dn, G) (xs @ [x]) = check_and_apply (dn', G') x\<close>
  using assms by auto

text \<open>For a correct peer, the hash nodes in the delivered nodes are always equal to the hash nodes in the local graph.\<close>

lemma check_and_apply_preserve_same_nodes:
  assumes \<open>check_and_apply (ah, G) n = (ah', G')\<close>
     and \<open>fset_of_list ah = G\<close>
   shows \<open>fset_of_list ah' = G'\<close>
  by (metis assms(1) assms(2) check_and_apply.simps fset_of_list_append fset_of_list_simps(1) fset_of_list_simps(2) split_pairs)

lemma apply_history_preserve_same_nodes:
  assumes \<open>apply_history (ah, G) ns = (ah', G')\<close>
    and \<open>fset_of_list ah = G\<close>
  shows \<open>fset_of_list ah' = G'\<close>
using assms proof (induction ns arbitrary: ah G ah' G')
  case Nil
  then show ?case
    by simp
next
  case (Cons a ns)
  then show ?case
    by (metis (mono_tags, lifting) apply_history.elims peers_with_arbitrary_history.check_and_apply.simps 
        peers_with_arbitrary_history_axioms check_and_apply_preserve_same_nodes foldl_Cons)
qed

lemma peer_apply_history_preserve_same_nodes:
  assumes \<open>apply_history ([], {||}) ns = (ah, G)\<close>
  shows \<open>fset_of_list ah = G\<close>
  using apply_history_preserve_same_nodes assms by auto

lemma in_history_in_graph:
  assumes \<open>n \<in> set (delivered_nodes i)\<close>
  shows \<open>n |\<in>| graph i\<close>
  by (metis delivered_nodes_def assms peers_with_arbitrary_history.graph_def peers_with_arbitrary_history_axioms fset_of_list.rep_eq peer_apply_history_preserve_same_nodes peer_state.simps prod.collapse)

text \<open>A correct peer should always have a valid graph.\<close>

lemma check_and_apply_preserve_validity:
  assumes \<open>check_and_apply (ah, G) n = (ah', G')\<close>
    and \<open>valid_graph G\<close>
  shows \<open>valid_graph G'\<close>
  by (metis assms(1) assms(2) check_and_apply.simps prod.inject valid_graph.simps)

lemma apply_history_preserve_validity:
  assumes \<open>apply_history (ah, G) ns = (ah', G')\<close>
    and \<open>valid_graph G\<close>
  shows \<open>valid_graph G'\<close>
using assms proof (induction ns arbitrary: ah G ah' G')
  case Nil
  then show ?case 
    by auto
next
  case (Cons a ns)
  then show ?case
    by (metis (no_types, lifting) apply_history.elims peers_with_arbitrary_history.check_and_apply.simps 
        peers_with_arbitrary_history_axioms foldl_Cons valid_graph.intros(2))
qed

text \<open>The items in the delivered nodes of a correct peer are all distinct, i.e that is does not contain the same item more than once. \<close>

lemma check_and_apply_preserve_distinctness:
  assumes \<open>check_and_apply (ah, G) n = (ah', G')\<close>
     and \<open>fset_of_list ah = G\<close>
     and \<open>distinct ah\<close>
   shows \<open>distinct ah'\<close>
  by (metis Int_insert_right_if0 append.right_neutral assms check_and_apply.simps distinct_append   
      distinct_singleton fset_of_list.rep_eq is_struct_valid.elims(2) is_valid.elims(2) list.simps(15) prod.sel(1))

lemma apply_history_preserve_distinctness:
  assumes \<open>apply_history (ah, G) ns = (ah', G')\<close>
    and \<open>fset_of_list ah = G\<close>
    and \<open>distinct ah\<close>
  shows \<open>distinct ah'\<close>
  using assms proof (induction ns arbitrary: ah G ah' G')
  case Nil
  then show ?case 
    by simp
next
  case (Cons a ns)
  then show ?case
    by (metis (no_types, opaque_lifting) apply_history.simps peers_with_arbitrary_history.check_and_apply_preserve_same_nodes peers_with_arbitrary_history_axioms check_and_apply_preserve_distinctness foldl_Cons old.prod.exhaust)
qed

text \<open>The delivered nodes of a correct peer is also consistent causally consistent\<close>

lemma ancestor_reachable_nodes_of:
  \<open>reachable_nodes_of node - {node} = ancestor_nodes_of node\<close>
proof
  show \<open>reachable_nodes_of node - {node} \<subseteq> ancestor_nodes_of node\<close>
    by (metis DiffE ancestor_nodes_of_def bot_fset.rep_eq finsert_iff fset_simps(2) hash_graph.reachable_def 
        hash_graph_axioms mem_Collect_eq reachable_nodes_of_def subsetI)
next
  show \<open>ancestor_nodes_of node \<subseteq> reachable_nodes_of node - {node}\<close>
    by (metis (no_types, lifting) Collect_mono_iff Diff_empty ancestor_nodes_of_def mem_Collect_eq 
        no_cycle reachable_def reachable_nodes_of_def subset_Diff_insert)
qed

lemma valid_node_ancestors_in_G:
  \<open>valid_graph G \<Longrightarrow> is_valid G n \<Longrightarrow> ancestor_nodes_of n \<subseteq> fset G\<close>
  by (metis ancestor_reachable_nodes_of peers_with_arbitrary_history.valid_graph.intros(2) 
      peers_with_arbitrary_history_axioms finsert_iff fset_simps(2) funion_finsert_right node_reachable_of_itself 
      reachable_of_G_node_in_G subset_insert_iff sup_bot.right_neutral valid_graph_implies_struct_valid)

lemma valid_history_causality_hold1:
  \<open>valid_graph G \<Longrightarrow> is_valid G x \<Longrightarrow> \<forall>y. y \<prec> x \<longrightarrow> y \<in> fset G\<close>
  by (metis CollectI hash_graph.ancestor_nodes_of_def hash_graph_axioms subsetD valid_node_ancestors_in_G)

lemma valid_history_causality_hold2:
  \<open>valid_graph G \<Longrightarrow> is_valid G x \<Longrightarrow> \<forall>y \<in> fset G . y \<prec> x \<or> y \<parallel> x\<close>
  by (metis (no_types, lifting) CollectI is_concurrent_def is_struct_valid.elims(2) is_valid.elims(2) reachable_def reachable_nodes_of_def reachable_of_G_node_in_G subset_eq valid_graph_implies_struct_valid)

lemma check_and_apply_preserve_causal_consistency:
  assumes \<open>valid_graph G\<close>
     and \<open>check_and_apply (ah, G) x = (ah', G')\<close>
     and \<open>fset_of_list ah = G\<close>
     and \<open>hb.hb_consistent ah\<close>
   shows \<open>hb.hb_consistent ah'\<close>
proof (cases \<open>is_valid G x\<close>)
  case True
  have \<open>\<forall>y \<in> fset G. y \<prec> x \<or> x \<parallel> y\<close>
    using True assms(1) is_concurrent_def valid_history_causality_hold2 by blast 
  then show ?thesis
    by (metis assms(2) assms(3) assms(4) check_and_apply.simps fset_of_list.rep_eq fst_conv hb.dual_order.asym hb.hb_consistent.simps is_concurrent_def)
next
  case False
  then show ?thesis
    using assms(2) assms(4) by auto
qed

lemma apply_history_preserve_causal_consistency:
  assumes \<open>valid_graph G\<close>
     and \<open>apply_history (ah, G) ns = (ah', G')\<close>
     and \<open>fset_of_list ah = G\<close>
     and \<open>hb.hb_consistent ah\<close>
   shows \<open>hb.hb_consistent ah'\<close>
  using assms proof (induction ns arbitrary: ah G ah' G')
  case Nil
  then show ?case by simp
next
  case (Cons a ns)
  then show ?case
    by (metis (mono_tags, lifting) apply_history.elims peers_with_arbitrary_history.check_and_apply_preserve_causal_consistency peers_with_arbitrary_history_axioms check_and_apply.simps check_and_apply_preserve_validity foldl_Cons fset_of_list_append fset_of_list_simps(1) fset_of_list_simps(2))
qed

lemma peer_history_hb_consistent:
  assumes \<open>apply_history ([], {||}) ns = (ah, G)\<close>
  shows \<open>hb.hb_consistent ah\<close>
  using apply_history_preserve_causal_consistency assms fset_of_list_simps(1) valid_graph.intros(1) by blast

lemma hb_consistent_ops:  \<open>hb.hb_consistent (delivered_nodes i)\<close>
  by (metis peers_with_arbitrary_history.delivered_nodes_def peers_with_arbitrary_history.peer_history_hb_consistent peers_with_arbitrary_history_axioms peer_state.simps prod.collapse)

subsection \<open>Convergence\<close>

text \<open>
  We can now prove the convergence theorem, which adds Byzantine fault tolerance to the abstract 
  convergence theorem from~\cite{gomes2017verifying}. The theorem states that for two correct peers, 
  if all concurrent operations commute, and the heads of the graphs of the two peers are equal, they 
  reach the same final CRDT state.
\<close>

lemma convergence:
  assumes \<open>hb.concurrent_ops_commute (delivered_nodes i)\<close>
    and \<open>hb.concurrent_ops_commute (delivered_nodes j)\<close>
    and \<open>heads (graph i) = heads (graph j)\<close>
  shows \<open>apply_operations (delivered_nodes i) = apply_operations (delivered_nodes j)\<close>
proof -
  have sv: \<open>struct_valid (graph i) \<and> struct_valid (graph j)\<close>
    by (metis apply_history_preserve_validity peers_with_arbitrary_history.graph_def peers_with_arbitrary_history_axioms peer_state.simps prod.collapse valid_graph.intros(1) valid_graph_implies_struct_valid)
  have \<open>graph i = graph j\<close>
    using heads_define_graph[of \<open>graph i\<close> \<open>graph j\<close>] by (simp add: sv assms hash_no_collisions)
  then have 1: \<open>set (delivered_nodes i) = set (delivered_nodes j)\<close>
    by (metis apply_history_preserve_same_nodes peers_with_arbitrary_history.delivered_nodes_def peers_with_arbitrary_history_axioms fset_of_list.rep_eq fset_of_list_simps(1) local.graph_def peer_state.simps prod.collapse)
  then have 2: \<open>distinct (delivered_nodes i) \<and> distinct (delivered_nodes j)\<close>
    by (metis apply_history_preserve_distinctness peers_with_arbitrary_history.delivered_nodes_def peers_with_arbitrary_history_axioms distinct.simps(1) fset_of_list_simps(1) peer_state.simps prod.collapse)
  then have \<open>hb.hb_consistent (delivered_nodes i) \<and> hb.hb_consistent (delivered_nodes j)\<close>
    using hb_consistent_ops by auto
  then show ?thesis 
    by (metis 1 2 apply_operations_def assms(1) assms(2) hb.convergence)
qed

subsection \<open>Synchronization\<close>
text \<open>
  While we have proven the convergence theorem, which states that two correct peers reach the same 
  state if the CRDT algorithm ensures $\isa{concurrent-ops-commute}$ and the peers have the same heads, 
  an attacker could potentially prevent two correct peers from having the same heads. We need to prove 
  that two correct peers can always synchronize to the same heads.

  The synchronization process involves the following steps:

  \begin{itemize}
  \item Peers periodically exchange their current heads.
  \item When a peer receives heads from another peer, it compares them with its own.
  \item If there are differences, the peer requests the missing nodes from the other peer. Previous 
  work~\cite{kleppmann2020byzantine} has proposed optimized algorithms to quickly identify the nodes 
  that are missing from each peer's graph and efficiently transmit only those nodes, but for the 
  purpose of this proof any reconciliation is sufficient.
  \item Upon receiving the missing nodes, the peer validates them and incorporates them into its own graph.
  \end{itemize}
 

  Since we assume the attacker cannot prevent correct peers from communicating, exchanging the missing 
  nodes from each other is guaranteed to succeed. However, the attacker could attempt to construct 
  a hash node that passes the validity check of node $i$, but fails the validity check of node $j$, 
  thus preventing node $j$ from adding the hash node to its graph. 

  More specifically, the attacker cannot prevent correct peers from failing the structural validity 
  check. This is because structural validity only requires that a node's predecessors exist before 
  it is added to the graph, the same node is not added more than once, and a node does not reference 
  the hash of itself (which is computationally infeasible). As long as missing nodes are added in an 
  order that is consistent with the ${\isa{happens-before}}$ relation, structural validity is guaranteed.

  The real issue lies in semantic validity. It is conceivable that an attacker could construct a node 
  that passes the semantic validity check on peer $i$ but fails it on peer $j$.

  To address this concern, we need to ensure that semantic validity checks are consistent across 
  all correct peers. That is, two correct peers always make the same decision on whether or not a 
  node is valid. This leads us to an important property of our BFT system: the semantic validity of 
  a node must be deterministic and based solely on the information contained within the node and its 
  ancestors in the hash graph. This criterion was proposed informally by Kleppmann~\cite{kleppmann2022making}, 
  and we now formalise it in our proof framework and show on this affects the synchronization process.

  We capture this property by an assumption that only ancestors are relevant to semantic validity: 
  the validity of node $n$ does not change when any nodes that are concurrent with $n$ are added to the graph. 

  CRDT algorithms that use a semantic validity check must then prove that it satifies this property.
\<close> 

definition only_ancestors_relevant :: \<open>bool\<close> where 
  \<open>only_ancestors_relevant = (\<forall>n G. (ancestor_nodes_of n) \<subseteq> fset G \<longrightarrow> 
  is_sem_valid_set (ancestor_nodes_of n) n \<longleftrightarrow> is_sem_valid G n)\<close>

lemma only_ancestors_relevant':
  assumes \<open>only_ancestors_relevant\<close>
  shows \<open>((ancestor_nodes_of n) \<subseteq> fset G \<Longrightarrow> 
  is_sem_valid_set (ancestor_nodes_of n) n \<longleftrightarrow> is_sem_valid G n)\<close>
  using assms only_ancestors_relevant_def by blast

lemma sem_valid_preserves:
  assumes \<open>valid_graph G\<close>
    and \<open>n |\<in>| G\<close>
    and \<open>only_ancestors_relevant\<close>
  shows \<open>is_sem_valid G n\<close>
using assms proof(induction G rule: valid_graph.induct)
  case 1
  then show ?case
    by blast
next
  case (2 G n)
  then show ?case
    by (metis (mono_tags, lifting) ancestor_reachable_nodes_of finsert_iff fset_simps(2) 
        funion_finsert_right is_valid.elims(2) node_reachable_of_itself reachable_of_G_node_in_G 
        assms(3) only_ancestors_relevant' subset_insert_iff sup.coboundedI1 sup_bot.right_neutral sup_fset.rep_eq valid_graph_implies_struct_valid valid_node_ancestors_in_G)
qed

lemma struct_valid_implies_ancestor_subset:
  assumes \<open>valid_graph G\<close>
    and \<open>is_struct_valid G n\<close>
  shows \<open>(ancestor_nodes_of n) \<subseteq> fset G\<close>
proof -
  have \<open>(\<forall>h |\<in>| fst n. \<exists>n |\<in>| G. H n = h)\<close>
    by (metis assms(2) fst_conv is_struct_valid.elims(2))
  then have \<open>preds_of_node n \<subseteq> fset G\<close>
    using hash_graph.preds_of_node_def hash_graph_axioms hash_no_collisions by blast
  then have \<open>\<forall>pred \<in>(preds_of_node n). reachable_nodes_of pred \<subseteq> fset G\<close>
    using assms(1) reachable_of_G_node_in_G by blast
  then have 1: \<open>reachable_nodes_of_set (preds_of_node n) \<subseteq> fset G\<close>
    using hash_graph.reachable_nodes_of_set_def hash_graph_axioms by fastforce
  then have \<open>reachable_nodes_of_set (preds_of_node n) \<union> {n} = reachable_nodes_of n\<close>
    using reachable_nodes_preds_equiv by auto
  then show ?thesis
    by (metis Diff_insert_absorb Un_insert_right 1 ancestor_reachable_nodes_of assms(2) 
        is_struct_valid.elims(2) subset_eq sup_bot.right_neutral)
qed

lemma sem_valid_consistent:
  assumes \<open>valid_graph G1\<close>
    and \<open>valid_graph G2\<close>
    and \<open>n |\<in>| G2\<close>
    and \<open>is_struct_valid G1 n\<close>
    and \<open>only_ancestors_relevant\<close>
  shows \<open>is_sem_valid G1 n\<close>
proof -
  have semn: \<open>is_sem_valid G2 n\<close>
    using assms(2) assms(3) assms(5) sem_valid_preserves by blast
  have ag2: \<open>(ancestor_nodes_of n) \<subseteq> fset G2\<close>
    by (metis ancestor_reachable_nodes_of assms(2) assms(3) peers_with_arbitrary_history.valid_graph_implies_struct_valid peers_with_arbitrary_history_axioms hash_graph.reachable_of_G_node_in_G hash_graph_axioms insert_Diff_single insert_subset)
  have \<open>(ancestor_nodes_of n) \<subseteq> fset G1\<close>
    using assms(1) assms(4) struct_valid_implies_ancestor_subset by blast
  then show ?thesis
    by (meson ag2 semn assms(5) only_ancestors_relevant')
qed

fun valid_seq :: \<open>(('hash, 'val) hash_graph \<Rightarrow> ('hash, 'val) node \<Rightarrow> bool) 
  \<Rightarrow> ('hash, 'val) hash_graph \<Rightarrow> ('hash, 'val) node list \<Rightarrow> bool\<close> where
  \<open>valid_seq f G [] = True\<close>
| \<open>valid_seq f G (x#xs) = 
  (if f G x then
    valid_seq f (G|\<union>|{|x|}) xs
  else
    False
)\<close>

definition struct_valid_seq :: \<open>('hash, 'val) hash_graph \<Rightarrow> ('hash, 'val) node list \<Rightarrow> bool\<close> where
  \<open>struct_valid_seq G ns \<equiv> valid_seq is_struct_valid G ns\<close>

definition sem_valid_seq :: \<open>('hash, 'val) hash_graph \<Rightarrow> ('hash, 'val) node list \<Rightarrow> bool\<close> where
  \<open>sem_valid_seq G ns \<equiv> valid_seq is_sem_valid G ns\<close>

lemma valid_seq_fails:
  assumes \<open>\<not>(valid_seq f G xs)\<close>
  shows \<open>\<not>(valid_seq f G (xs@ys))\<close>
using assms proof (induction f G xs arbitrary: ys rule: valid_seq.induct)
  case (1 f G)
  then show ?case 
    by auto
next
  case (2 f G x xs)
  then show ?case
    by auto
qed

lemma struct_valid_seq_concat:
  assumes \<open>struct_valid G\<close>
    and \<open>struct_valid_seq G xs\<close>
  shows \<open>struct_valid_seq G (xs@ys) = struct_valid_seq (G |\<union>| (fset_of_list xs)) ys\<close>
using assms proof (induction xs arbitrary: G ys rule: rev_induct)
  case Nil
  then show ?case 
    by simp
next
  case (snoc x xs)
  have \<open>struct_valid_seq G xs\<close>
    using snoc.prems(2) struct_valid_seq_def valid_seq_fails by blast
  then show ?case
    using snoc.IH snoc.prems(1) snoc.prems(2) struct_valid_seq_def by auto
qed

lemma sem_valid_seq_concat:
  assumes \<open>sem_valid G\<close>
    and \<open>sem_valid_seq G xs\<close>
  shows \<open>sem_valid_seq G (xs@ys) = sem_valid_seq (G |\<union>| (fset_of_list xs)) ys\<close>
using assms proof (induction xs arbitrary: G ys rule: rev_induct)
  case Nil
  then show ?case 
    by simp
next
  case (snoc x xs)
  have \<open>sem_valid_seq G xs\<close>
    using sem_valid_seq_def snoc.prems(2) valid_seq_fails by blast
  then show ?case
    using snoc.IH snoc.prems(1) snoc.prems(2) sem_valid_seq_def by auto
qed

lemma struct_valid_seq_valid_graph:
  assumes \<open>struct_valid G\<close>
    and \<open>struct_valid_seq G xs\<close>
  shows \<open>struct_valid (G |\<union>| (fset_of_list xs))\<close>
using assms proof (induction xs arbitrary: G rule: rev_induct)
  case Nil
  then show ?case 
    by simp
next
  case (snoc x xs)
  have 1: \<open>struct_valid_seq G xs\<close>
    using snoc.prems(2) struct_valid_seq_def valid_seq_fails by blast
  have 2: \<open>struct_valid (G |\<union>| fset_of_list xs)\<close>
    by (simp add: \<open>struct_valid_seq G xs\<close> snoc.IH snoc.prems(1))
  have 3: \<open>G |\<union>| fset_of_list (xs @ [x]) = (G |\<union>| fset_of_list xs) |\<union>| {|x|}\<close>
    by simp
  have 4: \<open>is_struct_valid (G |\<union>| fset_of_list xs) x\<close>
    by (metis 1 snoc.prems(1) snoc.prems(2) struct_valid_seq_concat struct_valid_seq_def valid_seq.simps(2))
  have \<open>struct_valid ((G |\<union>| fset_of_list xs) |\<union>| {|x|})\<close>
    by (metis 2 4 is_struct_valid.elims(2) struct_valid.simps)
  then show ?case
    by simp
qed

lemma sem_valid_seq_valid_graph:
  assumes \<open>sem_valid G\<close>
    and \<open>sem_valid_seq G xs\<close>
  shows \<open>sem_valid (G |\<union>| (fset_of_list xs))\<close>
using assms proof (induction xs arbitrary: G rule: rev_induct)
  case Nil
  then show ?case 
    by simp
next
  case (snoc x xs)
  have 1: \<open>sem_valid_seq G xs\<close>
    using sem_valid_seq_def snoc.prems(2) valid_seq_fails by blast
  have 2: \<open>sem_valid (G |\<union>| fset_of_list xs)\<close>
    by (simp add: \<open>sem_valid_seq G xs\<close> snoc.IH snoc.prems(1))
  have 3: \<open>G |\<union>| fset_of_list (xs @ [x]) = (G |\<union>| fset_of_list xs) |\<union>| {|x|}\<close>
    by simp
  have 4: \<open>is_sem_valid (G |\<union>| fset_of_list xs) x\<close>
    by (metis 1 sem_valid_seq_concat sem_valid_seq_def snoc(2) snoc.prems(2) valid_seq.simps(2))
  have \<open>sem_valid ((G |\<union>| fset_of_list xs) |\<union>| {|x|})\<close>
    by (metis 2 4 sem_valid.simps)
  then show ?case
    by simp
qed

lemma sem_struct_valid_seq_get_valid_graph:
  assumes \<open>valid_graph G\<close>
    and \<open>sem_valid_seq G xs\<close>
    and \<open>struct_valid_seq G xs\<close>
  shows \<open>valid_graph (G |\<union>| (fset_of_list xs))\<close>
using assms proof (induction xs arbitrary: G rule: rev_induct)
  case Nil
  then show ?case
    by force
next
  case (snoc x xs)
  have 1: \<open>valid_graph G\<close>
    using snoc.prems(1) by blast
  have sem_v: \<open>sem_valid_seq G xs\<close>
    using sem_valid_seq_def snoc.prems(2) valid_seq_fails by blast
  then have 2: \<open>is_sem_valid (G |\<union>| (fset_of_list xs)) x\<close>
    by (metis 1  sem_valid_seq_concat sem_valid_seq_def snoc.prems(2) 
        valid_graph_implies_sem_valid valid_seq.simps(2))
  have str_v: \<open>struct_valid_seq G xs\<close>
    using snoc.prems(3) struct_valid_seq_def valid_seq_fails by blast
  then have 3: \<open>is_struct_valid (G |\<union>| (fset_of_list xs)) x\<close>
    by (metis snoc.prems(1) snoc.prems(3) struct_valid_seq_concat struct_valid_seq_def 
        valid_graph_implies_struct_valid valid_seq.simps(2))
  then show ?case
    by (metis 1 2 sem_v str_v append.right_neutral fset_of_list_append fset_of_list_simps(2) 
        funion_finsert_right is_valid.elims(3) snoc.IH sup_bot.right_neutral valid_graph.simps)
qed

lemma struct_valid_seq_implies_sem_valid_seq:
  assumes \<open>valid_graph G1\<close>
    and \<open>valid_graph G2\<close>
    and \<open>\<forall>n \<in> set xs. n |\<in>| G2\<close>
    and \<open>struct_valid_seq G1 xs\<close>
    and \<open>only_ancestors_relevant\<close>
  shows \<open>sem_valid_seq G1 xs\<close>
using assms proof (induction xs arbitrary: G1 G2 rule: rev_induct)
  case Nil
  then show ?case 
    using sem_valid_seq_def valid_seq.simps(1) by blast
next
  case (snoc x xs)
  have 1: \<open>struct_valid_seq G1 xs\<close>
    using snoc.prems(4) struct_valid_seq_def valid_seq_fails by blast
  then have 2: \<open>sem_valid_seq G1 xs\<close>
    using snoc.IH snoc.prems(1) snoc.prems(2) snoc.prems(3) snoc.prems(5) by auto
  then have 3: \<open>sem_valid_seq G1 (xs@[x]) = (sem_valid_seq (G1 |\<union>| (fset_of_list xs)) [x])\<close>
    using sem_valid_seq_concat snoc.prems(1) by auto
  then have 4: \<open>valid_graph (G1 |\<union>| (fset_of_list xs))\<close>
    by (simp add: 1 2 sem_struct_valid_seq_get_valid_graph snoc.prems(1))
  then have \<open>is_struct_valid (G1 |\<union>| (fset_of_list xs)) x\<close>
    by (metis 1 snoc.prems(1) snoc.prems(4) struct_valid_seq_concat struct_valid_seq_def 
        valid_graph_implies_struct_valid valid_seq.simps(2))
  then have \<open>is_sem_valid (G1 |\<union>| (fset_of_list xs)) x\<close>
    by (meson "4" assms(5) in_set_conv_decomp sem_valid_consistent snoc.prems(2) snoc.prems(3))
  then show ?case
    using "3" sem_valid_seq_def by force
qed

lemma synchronization:
  assumes \<open>only_ancestors_relevant\<close>
    and \<open>valid_graph G1\<close>
    and \<open>valid_graph G2\<close>
    and \<open>fset_of_list xs = G2 |-| G1\<close>
    and \<open>struct_valid_seq G1 xs\<close>
  shows \<open>sem_valid_seq G1 xs\<close>
  by (metis assms fminus_iff fset_of_list.rep_eq peers_with_arbitrary_history.struct_valid_seq_implies_sem_valid_seq 
      peers_with_arbitrary_history_axioms)

text \<open>
  The theorem states that if $xs$ can be applied to G1 in a structurally valid order, then $xs$ is 
  guaranteed to be semantically valid with respect to G1. This means that peer 1 can apply all 
  the missing nodes from peer 2's graph to its own graph. As the theorem is symmetric, the same 
  principle applies in reverse: peer 2 can apply all the nodes it's missing from peer 1's graph.

  This leads to a conclusion: as long as semantic validity is only dependent on ancestors, we can 
  guarantee that any two correct peers will be able to synchronize to identical graphs, i.e Byzantine 
  peers cannot prevent correct peers from synchronizing thier hash graph heads. 
\<close>

end

subsection \<open>BFT Strong Eventual Consistency\<close>

text \<open>To achieve BFT strong eventual consistency, the CRDT algorithm must satisfy the following properties:\<close>

locale bft_strong_eventual_consistency = peers_with_arbitrary_history +
  assumes sem_check_only_ancestors_relevant: 
    \<open>(ancestor_nodes_of n) \<subseteq> fset G \<Longrightarrow> is_sem_valid_set (ancestor_nodes_of n) n \<longleftrightarrow> is_sem_valid G n\<close>
  assumes concurrent_opers_commute: \<open>hb.concurrent_ops_commute (delivered_nodes i)\<close>
  assumes step_never_fails: \<open>apply_history ([], {||}) ns = (dn, G) \<Longrightarrow> no_failure dn \<Longrightarrow>
    check_and_apply (dn, G) (hs, v) = (dn', G') \<Longrightarrow> no_failure dn'\<close>
begin

text \<open>
  The $\isa{concurrent-ops-commute}$ property is required to ensure that the operations can be executed 
  in any causal order without affecting the final state. The $\isa{only-ancestors-relevant}$ property 
  is required to ensure that the validity of a node is consistent across different valid graphs, so 
  that the Byzantine peers cannot prevent the correct peers from synchronizing their hash graph heads. 

  The convergence theorem and synchronization theorem prove that two correct peers can reach the same 
  state, but this does not exclude the possibility that the state is a failure state. Therefore, the 
  $\isa{step-never-fails}$ property, which is not discuess in the previous sections, is required to 
  ensure that the correct peers never reach failure state.
\<close>

theorem sec_convergence:
  assumes \<open>heads (graph i) = heads (graph j)\<close>
  shows \<open>apply_operations (delivered_nodes i) = apply_operations (delivered_nodes j)\<close>
  by (metis assms concurrent_opers_commute convergence)

lemma apply_history_never_fails:
  assumes \<open>apply_history ([], {||}) ns = (dn, G)\<close>
  shows \<open>no_failure dn\<close>
using assms proof (induction ns arbitrary: dn G rule: rev_induct)
  case Nil
  then show ?case
    by (simp add: initial_state_no_failure)
next
  case (snoc x xs)
  obtain dn' G' where \<open>apply_history ([], {||}) xs = (dn', G')\<close>
    by fastforce
  then have \<open>no_failure dn'\<close>
    using snoc(1) by blast
  then show ?case
    by (metis \<open>apply_history ([], {||}) xs = (dn', G')\<close> apply_history_snoc old.prod.exhaust snoc.prems step_never_fails)
qed

theorem sec_progress: \<open>apply_operations (delivered_nodes i) \<noteq> None\<close>
  by (metis apply_history_never_fails apply_operations_def no_failure_def peer_state.simps peers_with_arbitrary_history.delivered_nodes_def peers_with_arbitrary_history_axioms prod.exhaust_sel)

theorem sec_synchronization:
  assumes \<open>fset_of_list xs = (graph j) |-| (graph i)\<close>
    and \<open>struct_valid_seq (graph i) xs\<close>
  shows \<open>sem_valid_seq (graph i) xs\<close>
  by (metis assms(1) assms(2) local.graph_def only_ancestors_relevant_def 
      peers_with_arbitrary_history.apply_history_preserve_validity peers_with_arbitrary_history.peer_state.simps 
      peers_with_arbitrary_history_axioms prod.collapse sem_check_only_ancestors_relevant synchronization valid_graph.intros(1))

end

end