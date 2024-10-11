(* Liangrun Da, Technical University of Munich
   Martin Kleppmann, University of Cambridge
*)
theory Hash_Graph
  imports Main "HOL-Library.FSet"
begin

section \<open>Hash Graph\<close>

subsection \<open>Hash Graph Definition\<close>

text \<open>
  We use a Hash DAG as the underlying data structure for various purposes, including tracking the 
  causal relationships between operations, ensuring the eventual delivery of updates, and providing 
  a foundation for validity checks of incoming updates.

  A hash node is a pair of a finite set of hashes and a value. The set of hashes represent the 
  predecessors of the node in the graph, and the value is the value associated with this node, 
  e.g a CRDT operation. A hash graph is a finite set of hash nodes.
\<close>

type_synonym ('hash, 'val) node = \<open>('hash fset \<times> 'val)\<close>
type_synonym ('hash, 'val) hash_graph = \<open>('hash, 'val) node fset\<close>
type_synonym ('hash, 'val) hash_func = \<open>('hash, 'val) node \<Rightarrow> 'hash\<close>
type_synonym ('hash, 'val) causal_func = \<open>('hash, 'val) node \<Rightarrow>('hash, 'val) node \<Rightarrow> bool\<close>

text \<open>
  We define the locale of the hash graph, assuming the hash function is collision-free. Although, 
  in theory, hash functions may have collisions, with cryptographic hash functions such as SHA-3 it 
  is generally believed to be computationally infeasible to find them with better than negligible 
  probability. Therefore, for the purposes of our formalization, we can safely assume that collisions 
  do not occur.
\<close>

locale hash_graph =
  fixes H :: \<open>('hash, 'val) hash_func\<close>
  assumes hash_no_collisions : \<open>(\<forall>x y. H x = H y \<longrightarrow> x = y)\<close>
begin

subsection \<open>Heads and Predecessors\<close>

text \<open>Head nodes are nodes that are not referenced by any other node in the graph.\<close>

definition head_nodes :: \<open>('hash, 'val) hash_graph \<Rightarrow> ('hash, 'val) node fset\<close>  where
  \<open>head_nodes G =FSet.ffilter (\<lambda>n. \<not>(\<exists>(hashes, _) |\<in>| G. H n |\<in>| hashes)) G\<close>

definition heads :: \<open>('hash, 'val) hash_graph \<Rightarrow> 'hash fset\<close> where
  \<open>heads G = H |`| (head_nodes G)\<close>

lemma head_nodes_iff: \<open>x |\<in>| head_nodes G \<longleftrightarrow> x |\<in>| G \<and> \<not>(\<exists>(hashes, _) |\<in>| G. H x |\<in>| hashes)\<close>
  using head_nodes_def by fastforce

lemma heads_iff: \<open>x |\<in>| G \<and> \<not>(\<exists>(hashes, _) |\<in>| G. H x |\<in>| hashes) \<longleftrightarrow> H x |\<in>| heads G\<close>
proof 
  assume assm: \<open>x |\<in>| G \<and> \<not> (\<exists>(hashes, _)|\<in>|G. H x |\<in>| hashes)\<close>
  show \<open>H x |\<in>| heads G\<close>  by (simp add: assm head_nodes_iff heads_def)
next
  assume assm: \<open>H x |\<in>| heads G\<close>
  show \<open>x |\<in>| G \<and> \<not> (\<exists>(hashes, _)|\<in>|G. H x |\<in>| hashes)\<close>
    by (metis (mono_tags, lifting) assm fimage_iff hash_no_collisions head_nodes_iff heads_def)
qed

text \<open>We also define set versions of $head-nodes$ and $heads$ for convenience.\<close>

definition head_nodes_set :: \<open>('hash, 'val) hash_graph \<Rightarrow> ('hash, 'val) node set\<close> where
  \<open>head_nodes_set G = fset (FSet.ffilter (\<lambda>n. \<not>(\<exists>(hashes, _) |\<in>| G. H n |\<in>| hashes)) G)\<close>

definition heads_set :: \<open>('hash, 'val) hash_graph \<Rightarrow> 'hash set\<close> where
  \<open>heads_set G = fset (H |`| (head_nodes G))\<close>

definition preds_of_node :: \<open>('hash, 'val) node \<Rightarrow> ('hash, 'val) node set\<close> where
  \<open>preds_of_node node \<equiv> {x. H x |\<in>| fst node}\<close>

subsection \<open>Structural Validity\<close>

text \<open> 
  A hash graph is defined to be structurally valid if it is either empty, or it is obtained by 
  extending a valid hash graph by a new hash node that satisfies the following conditions, 
  which can easily be enforced in practice:

  \begin{itemize}
      \item All the hashes in the new node resolve to nodes that are already in the graph, i.e the 
      predecessors of the new node are in the graph.
      \item The new node itself is not in the graph.
      \item The hash of the new node is not in the set of hashes of the new node, i.e it doesn't 
      reference itself. Constructing a node that references itself is similar to constructing a hash 
      collision, and is also believed to be computationally infeasible. For the sake of proof, it is 
      convenient to make this a separate assumption. 
  \end{itemize}
  \<close>

inductive struct_valid :: \<open>('hash, 'val) hash_graph \<Rightarrow> bool\<close> where
  empty_graph: \<open>struct_valid {||}\<close> |
  extend_graph: \<open>\<lbrakk>struct_valid G;
                  \<forall>h |\<in>| hashes. \<exists>n |\<in>| G. H n = h;
                  (hashes, val) |\<notin>| G;
                  H (hashes, val) |\<notin>| hashes
                 \<rbrakk> \<Longrightarrow> struct_valid (G |\<union>| {|(hashes, val) |})\<close>

fun is_struct_valid :: \<open>('hash, 'val) hash_graph \<Rightarrow> ('hash, 'val) node \<Rightarrow> bool\<close> where
  \<open>is_struct_valid G (hashes, val) = (
    (\<forall>h |\<in>| hashes. \<exists>n |\<in>| G. H n = h) \<and>
    (hashes, val) |\<notin>| G \<and>
    H (hashes, val) |\<notin>| hashes
  )\<close>

inductive_cases struct_valid_indcases: \<open>struct_valid G\<close>

lemma graph_hashes_closed:
  assumes \<open>struct_valid G\<close>
    and \<open>(hashes, val) |\<in>| G\<close>
    and \<open>h |\<in>| hashes\<close>
  shows \<open>\<exists>n |\<in>| G. H n = h\<close>
using assms proof(induction rule: struct_valid.induct)
  case (empty_graph )
  then show ?case by force
next
  case (extend_graph G hashes val)
  then show ?case by auto
qed

lemma node_not_referencing_itself:
  assumes \<open>struct_valid G\<close>
  shows \<open>\<forall>(hashes, val) |\<in>| G. H (hashes, val) |\<notin>| hashes\<close>
using assms proof(induction rule: struct_valid.induct)
  case (empty_graph)
  then show ?case by simp
next
  case (extend_graph G hashes val)
  then show ?case by fastforce
qed

lemma old_nodes_not_referencing_new_node:
  assumes \<open>struct_valid G\<close>
    and \<open>node |\<notin>| G\<close>
    and \<open>struct_valid (G |\<union>| {|node|})\<close>
  shows \<open>\<forall>(hs, val) |\<in>| G. H node |\<notin>| hs\<close>
proof (rule ccontr)
  assume \<open>\<not> (\<forall>(hs, val)|\<in>|G. H node |\<notin>| hs)\<close>
  then have \<open>\<exists>(hs, val)|\<in>|G. H node |\<in>| hs\<close> by blast
  then show \<open>False\<close>
    by (metis (no_types, lifting) hash_graph.hash_no_collisions hash_graph_axioms assms(1) assms(2) 
        case_prodE graph_hashes_closed)
qed

lemma new_node_is_head_node:
  assumes \<open>struct_valid G\<close>
    and \<open>(hashes, val) |\<notin>| G\<close>
    and \<open>struct_valid (G |\<union>| {|(hashes, val)|})\<close>
  shows \<open>(hashes, val) |\<in>| head_nodes (G |\<union>| {|(hashes, val)|})\<close>
proof -
  have \<open>\<not>(\<exists>(hs, v) |\<in>| G. H (hashes, val) |\<in>| hs)\<close>
    using assms old_nodes_not_referencing_new_node by fastforce
  moreover have \<open>H (hashes, val) |\<notin>| hashes\<close> 
    using assms(3) node_not_referencing_itself by fastforce
  moreover have \<open>\<not>(\<exists>(hs, v) |\<in>| (G |\<union>| {|(hashes, val)|}). H (hashes, val) |\<in>| hs)\<close>
    using calculation by force
  ultimately show ?thesis
    by (simp add: head_nodes_def)
qed

lemma new_node_in_head:
  assumes \<open>struct_valid G\<close>
    and \<open>(hashes, val) |\<notin>| G\<close>
    and \<open>struct_valid (G |\<union>| {|(hashes, val)|})\<close>
  shows \<open>H (hashes, val) |\<in>| heads (G |\<union>| {|(hashes, val)|})\<close>
  using assms(1) assms(2) assms(3) heads_def new_node_is_head_node by auto

lemma exclude_preds_from_heads_after_adding_new_node:
  assumes \<open>struct_valid G\<close>
    and \<open>(hashes, val) |\<notin>| G\<close>
    and \<open>struct_valid (G |\<union>| {|(hashes, val)|})\<close>
  shows \<open>\<not>(\<exists>x \<in> preds_of_node (hashes, val). x \<in> head_nodes_set (G |\<union>| {|(hashes, val)|}))\<close>
proof
  assume \<open>\<exists>x \<in> preds_of_node (hashes, val). x \<in> head_nodes_set (G |\<union>| {|(hashes, val)|})\<close>
  then obtain x where \<open>x \<in> preds_of_node (hashes, val)\<close> 
    and x_d2: \<open>x \<in> head_nodes_set (G |\<union>| {|(hashes, val)|})\<close>
    by blast
  then have \<open>H x |\<in>| hashes\<close> 
    using preds_of_node_def by fastforce
  then show \<open>False\<close>
    using x_d2 head_nodes_set_def by auto
qed

lemma not_head_remains_not_head_on_new_node_addition:
  assumes \<open>struct_valid G\<close>
    and \<open>(hashes, val) |\<notin>| G\<close>
    and \<open>struct_valid (G |\<union>| {|(hashes, val)|})\<close>
    and \<open>node \<in> fset G\<close>
    and \<open>node \<notin> head_nodes_set G\<close>
  shows \<open>node \<notin> head_nodes_set (G |\<union>| {|(hashes, val)|})\<close>
proof
  assume assm_contr: \<open>node \<in> head_nodes_set (G |\<union>| {|(hashes, val)|})\<close>
  have \<open>\<exists>x |\<in>| G. H node |\<in>| fst x\<close>
    using assms(4) assms(5) hash_graph.head_nodes_set_def hash_graph_axioms by fastforce
  moreover have \<open>\<not>(\<exists>x |\<in>| (G |\<union>| {|(hashes, val)|}). H node |\<in>| fst x)\<close>
    by (metis (no_types, lifting) assm_contr head_nodes_def head_nodes_iff head_nodes_set_def split_conv split_pairs)
  ultimately show \<open>False\<close> 
    by blast
qed 

lemma head_nodes_update_on_new_node_addition:
  assumes \<open>struct_valid G\<close>
    and \<open>(hashes, val) |\<notin>| G\<close>
    and \<open>struct_valid (G |\<union>| {|(hashes, val)|})\<close>
  shows \<open>head_nodes_set (G |\<union>| {|(hashes, val)|}) = head_nodes_set G - preds_of_node (hashes, val) \<union> {(hashes, val)}\<close>
proof 
  show \<open>head_nodes_set (G |\<union>| {|(hashes, val)|})
    \<subseteq> head_nodes_set G - preds_of_node (hashes, val) \<union> {(hashes, val)}\<close> 
  proof
    fix x
    assume x_d: \<open>x \<in> head_nodes_set (G |\<union>| {|(hashes, val)|})\<close>
    show \<open>x \<in> head_nodes_set G - preds_of_node (hashes, val) \<union> {(hashes, val)}\<close>
    proof (cases \<open>x = (hashes, val)\<close>)
      case True
      then show ?thesis 
        by blast
    next
      case False
      have \<open>x \<notin> preds_of_node (hashes, val)\<close> 
        using x_d assms exclude_preds_from_heads_after_adding_new_node by blast
      moreover have \<open>x \<notin> fset G - head_nodes_set G\<close>
        by (metis Diff_iff assms(1) assms(2) assms(3) not_head_remains_not_head_on_new_node_addition x_d)
      ultimately show ?thesis
        using head_nodes_set_def x_d by force
    qed
  qed
next
  show \<open> head_nodes_set G - preds_of_node (hashes, val) \<union> {(hashes, val)}
    \<subseteq> head_nodes_set (G |\<union>| {|(hashes, val)|}) \<close>
  proof
    fix x 
      assume x_a: \<open>x \<in> head_nodes_set G - preds_of_node (hashes, val) \<union> {(hashes, val)}\<close>
    show \<open>x \<in> head_nodes_set (G |\<union>| {|(hashes, val)|})\<close>
    proof (cases \<open>x = (hashes, val)\<close>)
      case True
      then show ?thesis 
        using assms hash_graph.head_nodes_def hash_graph.head_nodes_set_def hash_graph_axioms 
          new_node_is_head_node by blast
    next
      case False
      have x_not_n: \<open>x \<in> head_nodes_set G - preds_of_node (hashes, val)\<close>
        using False x_a by blast
      show \<open>x \<in> head_nodes_set (G |\<union>| {|(hashes, val)|})\<close>
        using head_nodes_set_def preds_of_node_def x_not_n by auto
    qed
  qed
qed

lemma nonempty_heads:
  assumes \<open>struct_valid G\<close> 
    and \<open>G \<noteq> {||}\<close>
  shows \<open>heads G \<noteq> {||}\<close>
using assms proof(induction rule: struct_valid.induct)
  case (empty_graph)
  then show ?case by auto
next
  case (extend_graph G hashes val)
  then show ?case
  proof (cases \<open>(hashes, val) |\<in>| G\<close>)
    case True
    then show ?thesis
      by (simp add: extend_graph.hyps(3))
  next
    case False
    then show ?thesis 
      by (metis extend_graph.hyps(1) extend_graph.hyps(2) extend_graph.hyps(4) 
          fempty_iff hash_graph.new_node_in_head hash_graph_axioms struct_valid.extend_graph)
  qed
qed

lemma empty_heads:
  assumes \<open>struct_valid G\<close>
  shows \<open>heads G = {||} \<longleftrightarrow> G = {||}\<close>
proof
  assume \<open>heads G = {||}\<close>
  then show \<open>G = {||}\<close>
    using assms nonempty_heads by blast
next
  assume \<open>G = {||}\<close>
  then show \<open>heads G = {||}\<close>
    by (metis equalsffemptyI fimage_is_fempty fminusE head_nodes_iff heads_def)
qed

subsection \<open>Ancestor and Reachability Relations\<close>

text \<open>
  The ancestor relation is defined inductively so that it is the transitive closure of the 
  predecessor relation. We also define the reachable relation as the reflexive transitive closure 
  of the predecessor relation. Two nodes are concurrent if neither of them is ancestor of the other.
\<close>

inductive ancestor :: \<open>('hash, 'val) node \<Rightarrow>('hash, 'val) node \<Rightarrow> bool\<close> (infix \<open>\<prec>\<close> 50) where
  pred: \<open>H a |\<in>| fst b \<Longrightarrow> a \<prec> b\<close> |
  tran: \<open>\<lbrakk>a \<prec> b; b \<prec> c\<rbrakk> \<Longrightarrow> a \<prec> c\<close>

definition reachable :: \<open>('hash, 'val) node \<Rightarrow>('hash, 'val) node \<Rightarrow> bool\<close> (infix \<open>\<preceq>\<close> 50) where
  \<open>a \<preceq> b \<equiv> a \<prec> b \<or> a = b\<close>

definition is_concurrent :: \<open>('hash, 'val) node \<Rightarrow>('hash, 'val) node \<Rightarrow> bool\<close> (infix \<open>\<parallel>\<close> 50) where
  \<open>a \<parallel> b \<equiv> \<not>(a \<prec> b) \<and> \<not>(b \<prec> a)\<close>

lemma ancestor_transitivity:
  assumes \<open>n1 \<prec> n2\<close>
    and \<open>n2 \<prec> n3\<close>
  shows \<open>n1 \<prec> n3\<close>
  using hash_graph.tran hash_graph_axioms assms(1) assms(2) by blast

lemma reachable_transitivity:
  assumes \<open>n1 \<preceq> n2\<close>
    and \<open>n2 \<preceq> n3\<close>
  shows \<open>n1 \<preceq> n3\<close>
  by (metis assms(1) assms(2) reachable_def tran)


lemma self_reachable: \<open>n \<preceq> n\<close>
  by (simp add: reachable_def)

lemma preds_of_node_reachable : \<open>\<forall> n1 \<in> preds_of_node n2. n1 \<preceq> n2\<close>
  by (simp add: hash_graph.preds_of_node_def hash_graph_axioms pred reachable_def)

definition reachable_nodes_of :: \<open>('hash, 'val) node \<Rightarrow> ('hash, 'val) node set\<close> where
  \<open>reachable_nodes_of node \<equiv> {x. x \<preceq> node}\<close>

definition ancestor_nodes_of :: \<open>('hash, 'val) node \<Rightarrow> ('hash, 'val) node set\<close> where
  \<open>ancestor_nodes_of node \<equiv> {x. x \<prec> node}\<close>

definition reachable_nodes_of_set :: \<open>('hash, 'val) node set \<Rightarrow> ('hash, 'val) node set\<close> where
  \<open>reachable_nodes_of_set nodes \<equiv> \<Union> (reachable_nodes_of ` nodes)\<close>

lemma reachable_nodes_exist_reachable_relation_iff: 
  \<open>x \<in> reachable_nodes_of_set nodes \<longleftrightarrow> (\<exists>y \<in> nodes. x \<preceq> y)\<close>
  by (simp add: reachable_nodes_of_def reachable_nodes_of_set_def)

lemma reachable_nodes_of_set_transitivity:
  assumes \<open>ns = preds_of_node node\<close>
  shows \<open>reachable_nodes_of_set ns \<subseteq> reachable_nodes_of node\<close>
proof
  fix x
  assume \<open>x \<in> reachable_nodes_of_set ns\<close>
  then have \<open>\<exists>y \<in> ns. x \<preceq> y\<close>
    by (simp add: reachable_nodes_of_def reachable_nodes_of_set_def)
  then obtain y where \<open>y \<in> ns\<close> and \<open>x \<preceq> y\<close>
    by blast
  then have \<open>y \<preceq> node\<close>
    using assms preds_of_node_reachable by blast
  then have \<open>x \<preceq> node\<close>
    using \<open>x \<preceq> y\<close> reachable_transitivity by blast
  show \<open>x \<in> reachable_nodes_of node\<close>
    by (simp add: \<open>reachable x node\<close> reachable_nodes_of_def)
qed

lemma indirect_predecessor_exists:
  assumes \<open>n1 \<prec> n2\<close>
    and \<open>n1 \<notin> preds_of_node n2\<close>
  shows \<open>\<exists>pred \<in> preds_of_node n2. (n1 \<prec> pred)\<close>
  using assms proof(induction rule: ancestor.induct)
  case (pred a b)
  then show ?case
    by (simp add: preds_of_node_def)
next
  case (tran a b c)
  then show ?case
    using ancestor.tran by blast
qed

lemma reachable_nodes_preds_equiv:
  assumes \<open>ns = preds_of_node n\<close>
  shows \<open>reachable_nodes_of_set ns \<union> {n} = reachable_nodes_of n\<close>
proof 
  show \<open>reachable_nodes_of_set ns \<union> {n} \<subseteq> reachable_nodes_of n\<close>
  proof
    fix x 
    assume assm1: \<open>x \<in> reachable_nodes_of_set ns \<union> {n}\<close>
    then show \<open>x \<in> reachable_nodes_of n\<close> 
    proof (cases \<open>x = n\<close>)
      case True
      have \<open>n \<preceq> n\<close>
        by (simp add: hash_graph.reachable_def hash_graph_axioms)
      then have \<open>n \<in> reachable_nodes_of n\<close>
        by (simp add: reachable_nodes_of_def)
      then show ?thesis
        by (simp add: True)
    next
      case False
      have 1: \<open>x \<in> reachable_nodes_of_set ns\<close>
        using False assm1 by auto
      obtain n' where \<open>n' \<in> ns \<and> x \<preceq> n'\<close>
        using 1 reachable_nodes_exist_reachable_relation_iff by auto
      then have \<open>n' \<preceq> n\<close>
        using assms preds_of_node_reachable by blast
      then show ?thesis
        using 1 assms reachable_nodes_of_set_transitivity by blast
    qed
  qed
next
  show \<open>reachable_nodes_of n \<subseteq> reachable_nodes_of_set ns \<union> {n}\<close>
  proof 
    fix x
    assume assm_x: \<open>x \<in> reachable_nodes_of n\<close>
    show \<open>x \<in> reachable_nodes_of_set ns \<union> {n}\<close>
    proof (cases \<open>x = n\<close>)
      case True
      then show ?thesis
        by auto
    next
      case False
      have \<open>x \<prec> n\<close>
        using False assm_x reachable_def reachable_nodes_of_def by auto
      have \<open>\<exists>n \<in> preds_of_node n. x \<preceq> n\<close>
        by (meson \<open>x \<prec> n\<close> indirect_predecessor_exists reachable_def)
      then obtain n' where n_d: \<open>n'\<in> preds_of_node n \<and> x \<preceq> n'\<close>
        by blast
      then have \<open>n' \<preceq> n\<close>
        by (simp add: preds_of_node_reachable)
      then show ?thesis 
        using assms n_d reachable_nodes_exist_reachable_relation_iff by auto
    qed
  qed
qed

lemma preds_of_G_node_in_G:
  assumes \<open>struct_valid G\<close>
    and \<open>(hashes, val) |\<in>| G\<close>
  shows \<open>preds_of_node (hashes, val) \<subseteq> fset G\<close>
proof
  fix x
  assume \<open>x \<in> preds_of_node (hashes, val)\<close>
  hence \<open>\<exists>pred_hash |\<in>| hashes. H x = pred_hash\<close>
    using preds_of_node_def by fastforce
  then obtain pred_hash where \<open>pred_hash |\<in>| hashes\<close> and \<open>H x = pred_hash\<close>
    by blast
  hence \<open>\<exists>p\<in> fset G. H p = pred_hash\<close>
    by (meson assms(1) assms(2) graph_hashes_closed)
  then show \<open>x |\<in>| G\<close>
    using \<open>H x = pred_hash\<close> hash_no_collisions by blast
qed

lemma reachable_of_G_node_in_G:
  assumes \<open>struct_valid G\<close>
    and \<open>n \<in> fset G\<close>
  shows \<open>reachable_nodes_of n \<subseteq> fset G\<close>
using assms proof(induction arbitrary: n rule: struct_valid.induct)
  case (empty_graph)
  then show ?case by simp
next
  case (extend_graph G hashes val)
  then show ?case
  proof (cases \<open>n = (hashes, val)\<close>)
    case True
    have \<open>reachable_nodes_of n = reachable_nodes_of_set (preds_of_node n) \<union> {n}\<close>
      using reachable_nodes_preds_equiv by blast
    moreover have \<open>\<forall>x \<in> preds_of_node n. x \<in> fset G\<close>
      using hash_graph.preds_of_node_def hash_graph_axioms True extend_graph.hyps(2) 
        hash_no_collisions by fastforce
    moreover have \<open>\<forall>x \<in> preds_of_node n. reachable_nodes_of x \<subseteq> fset G\<close>
      using calculation(2) extend_graph.IH by blast
    moreover have \<open>reachable_nodes_of_set (preds_of_node n) \<subseteq> fset G\<close>
      using reachable_nodes_of_set_def calculation(3) by fastforce
    ultimately show ?thesis using True by blast
  next
    case False
    then show ?thesis
      using extend_graph.IH extend_graph.prems by blast
  qed
qed

lemma node_reachable_of_itself:
  \<open>node \<in> reachable_nodes_of node\<close>
  by (simp add: hash_graph.self_reachable hash_graph_axioms reachable_nodes_of_def)

lemma reachable_union:
  assumes \<open>struct_valid G\<close>
  shows \<open>(reachable_nodes_of_set N) \<union> (reachable_nodes_of nn) = reachable_nodes_of_set (N \<union> {nn})\<close>
  by (simp add: Un_commute reachable_nodes_of_set_def)

lemma heads_subset_after_new_node_addition:
  assumes \<open>struct_valid G\<close>
    and \<open>(hs, v) |\<notin>| G\<close>
    and \<open>G' = G |\<union>| {|(hs, v)|}\<close>
    and \<open>struct_valid (G |\<union>| {|(hs, v)|})\<close>
  shows \<open>(reachable_nodes_of_set (head_nodes_set G)) \<union> {(hs, v)} 
    \<subseteq> reachable_nodes_of_set (head_nodes_set G')\<close>
proof
  fix x
  assume x_d: \<open>x \<in> reachable_nodes_of_set (head_nodes_set G) \<union> {(hs, v)}\<close>
  show \<open>x \<in> reachable_nodes_of_set (head_nodes_set G')\<close> 
  proof (cases \<open>x = (hs, v)\<close>)
    case T1: True
    then show ?thesis 
      by (metis UnI2 assms(1) assms(2) assms(3) assms(4) head_nodes_update_on_new_node_addition node_reachable_of_itself reachable_union)
  next
    case F1: False
    then have \<open>x \<in> reachable_nodes_of_set (head_nodes_set G)\<close>
      using x_d by auto
    then have \<open>\<exists>y \<in> (head_nodes_set G). x \<preceq> y\<close>
      using reachable_nodes_exist_reachable_relation_iff by blast
    then obtain y where \<open>y \<in> (head_nodes_set G)\<close> and \<open>x \<preceq> y\<close>
      by blast
    then show ?thesis 
    proof (cases \<open>y \<in> (head_nodes_set G')\<close>)
      case True
      then show ?thesis
        using \<open>x \<preceq> y\<close> reachable_nodes_exist_reachable_relation_iff by blast
    next
      case False
      have \<open>y \<in> preds_of_node (hs, v)\<close>
        using False \<open>y \<in> head_nodes_set G\<close> assms(1) assms(2) assms(3) assms(4) head_nodes_update_on_new_node_addition by force
      then have \<open>reachable y (hs, v)\<close>
        using preds_of_node_reachable by auto
      then have 1: \<open>x \<preceq> (hs, v)\<close>
        by (meson \<open>x \<preceq> y\<close> reachable_transitivity)
      have \<open>(hs, v) \<in> head_nodes_set G'\<close>
        using assms head_nodes_update_on_new_node_addition by fastforce
      then show ?thesis
        using 1 reachable_nodes_of_def reachable_nodes_of_set_def by blast
    qed
  qed
qed

lemma reachable_nodes_of_heads_is_subset_of_graph:
  assumes \<open>struct_valid G\<close>
  shows \<open>reachable_nodes_of_set (head_nodes_set G) \<subseteq> fset G\<close>
proof -
  have \<open>(head_nodes_set G) \<subseteq> fset G\<close>
    by (simp add: head_nodes_set_def)
  then have \<open>\<forall>n \<in> (head_nodes_set G). (reachable_nodes_of n) \<subseteq> fset G\<close>
    using assms reachable_of_G_node_in_G by blast
  then show ?thesis 
    using hash_graph.reachable_nodes_of_set_def hash_graph_axioms by fastforce
qed

lemma graph_is_subset_of_reachable_nodes_of_heads:
  assumes \<open>struct_valid G\<close>
  shows \<open>fset G \<subseteq> reachable_nodes_of_set (head_nodes_set G)\<close>
using assms proof(induction rule: struct_valid.induct)
  case empty_graph
  show ?case by auto
next
  case (extend_graph G hashes val)
  then show ?case proof (cases \<open>(hashes, val) |\<in>| G\<close>)
    case True
    then show ?thesis 
      using extend_graph.hyps(3) by auto
  next
    case False
    obtain G' where G'_d: \<open>G' = G |\<union>| {|(hashes, val)|}\<close>
      by blast
    have G_sub_headsG: \<open>fset G \<subseteq> reachable_nodes_of_set (head_nodes_set G)\<close>
      by (simp add: extend_graph.IH)
    moreover have \<open>reachable_nodes_of_set (head_nodes_set G') = (reachable_nodes_of_set (head_nodes_set G)) \<union> {(hashes, val)}\<close>
    proof 
      show \<open>reachable_nodes_of_set (head_nodes_set G')
    \<subseteq> reachable_nodes_of_set (head_nodes_set G) \<union> {(hashes, val)}\<close> 
      proof 
        fix x 
        assume x_d: \<open>x \<in> reachable_nodes_of_set (head_nodes_set G')\<close>
        show \<open>x \<in> reachable_nodes_of_set (head_nodes_set G) \<union> {(hashes, val)}\<close> 
        proof (cases \<open>x = (hashes, val)\<close>)
          case T1: True
          then show ?thesis by simp
        next
          case F1: False
          then obtain y where y_d: \<open>y \<in> (head_nodes_set G') \<and> x \<preceq> y\<close>
            using reachable_nodes_exist_reachable_relation_iff x_d by auto
          then show ?thesis 
          proof (cases \<open>y = (hashes, val)\<close>)
            case T2: True
            obtain z where z_d:\<open>z \<in> (preds_of_node y) \<and> x \<preceq> z\<close> 
              using F1 T2 hash_graph.indirect_predecessor_exists hash_graph.reachable_def hash_graph_axioms y_d by blast
            have \<open>z |\<in>| G\<close> 
            proof (rule ccontr)
              assume \<open>z |\<notin>| G\<close>
              then have \<open>\<not>struct_valid (G |\<union>| {|(hashes, val)|})\<close>
                using z_d fst_conv hash_graph.node_not_referencing_itself hash_graph.preds_of_node_def 
                  hash_graph_axioms preds_of_G_node_in_G T2 by fastforce
              then show \<open>False\<close> 
                using False extend_graph.hyps(1) extend_graph.hyps(2) extend_graph.hyps(4) hash_graph.extend_graph hash_graph_axioms by fastforce
            qed
            then have \<open>z \<in> (reachable_nodes_of_set (head_nodes_set G))\<close>
              using extend_graph.IH by blast
            then show ?thesis
              by (meson UnI1 reachable_nodes_exist_reachable_relation_iff reachable_transitivity z_d)
          next
            case F2: False
            have \<open>y \<in> (head_nodes_set G)\<close>
              using F2 G'_d head_nodes_set_def y_d by auto
            then show ?thesis
              using reachable_nodes_exist_reachable_relation_iff y_d by auto
          qed
        qed
      qed
    next
      show \<open>reachable_nodes_of_set (head_nodes_set G) \<union> {(hashes, val)}
    \<subseteq> reachable_nodes_of_set (head_nodes_set G')\<close>
        using False G'_d extend_graph.hyps(1) extend_graph.hyps(2) extend_graph.hyps(4) heads_subset_after_new_node_addition struct_valid.extend_graph by presburger
    qed
    moreover have \<open>fset G' = fset G \<union> {(hashes, val)}\<close>
      by (simp add: G'_d)
    ultimately show ?thesis 
      using G'_d by blast
  qed
qed

lemma reachable_nodes_of_heads_is_graph:
  assumes \<open>struct_valid G\<close>
  shows \<open>reachable_nodes_of_set (head_nodes_set G) = fset G\<close>
  using assms hash_graph.graph_is_subset_of_reachable_nodes_of_heads 
    hash_graph.reachable_nodes_of_heads_is_subset_of_graph hash_graph_axioms by blast

lemma heads_define_ancestors:
  assumes \<open>struct_valid G1\<close>
    and \<open>struct_valid G2\<close>
    and \<open>head_nodes_set G1 = head_nodes_set G2\<close>
  shows \<open>reachable_nodes_of_set (head_nodes_set G1) = reachable_nodes_of_set (head_nodes_set G2)\<close>
  by (simp add: assms(3))

lemma head_nodes_define_graph:
  assumes \<open>struct_valid G1\<close> and \<open>struct_valid G2\<close>
    and \<open>head_nodes G1 = head_nodes G2\<close>
  shows \<open>G1 = G2\<close>
  by (metis (no_types, lifting) reachable_nodes_of_heads_is_graph assms 
      fset_cong head_nodes_def head_nodes_set_def)

lemma head_hashes_defines_head_nodes:
  assumes \<open>heads G1 = heads G2\<close>
  shows \<open>head_nodes G1 = head_nodes G2\<close>
  by (metis assms fset.inj_map_strong hash_no_collisions heads_def)

text \<open>
  We finally reach an important conclusion that if two graphs are structurally valid and share the 
  same heads, the two must be equal. This theorem shows that when two peers need to synchronize their 
  updates, they can simply exchange the hashes of their head nodes. If these hashes are identical, 
  the nodes can be confident that their entire hash graphs, including all updates contained within 
  them, are exactly the same.
\<close>

theorem heads_define_graph:
  assumes \<open>struct_valid G1\<close> and \<open>struct_valid G2\<close>
    and \<open>heads G1 = heads G2\<close>
  shows \<open>G1 = G2\<close>
  by (metis assms head_hashes_defines_head_nodes head_nodes_define_graph)

subsection \<open>merge functions\<close>

text \<open>merge function works when both G1 and G2 are known to be valid\<close>

fun merge :: \<open>('hash, 'val) hash_graph \<Rightarrow> ('hash, 'val) hash_graph  \<Rightarrow> ('hash, 'val) hash_graph \<close> where
  \<open>merge G1 G2 = G1 |\<union>| G2\<close>

theorem merge_valid: 
  assumes \<open>struct_valid G1\<close>
    and \<open>struct_valid G2\<close>
  shows \<open>struct_valid (merge G1 G2)\<close>
using assms proof(induction G1 arbitrary: G2 rule: struct_valid.induct)
  case (empty_graph)
  then show ?case
    by auto
next
  case (extend_graph G hashes val)
  show ?case proof (cases \<open>(hashes, val) |\<in>| G2\<close>)
    case True
    then show ?thesis 
      by (metis extend_graph.IH extend_graph.prems finsert_absorb funion_finsert_left 
          funion_finsert_right merge.elims sup_bot_right)
  next
    case False
    have \<open>merge (G |\<union>| {|(hashes, val)|}) G2 = merge G G2 |\<union>| {|(hashes, val)|}\<close>
      by simp
    moreover have \<open>struct_valid (merge G G2)\<close>
      using extend_graph.IH extend_graph.prems by auto
    moreover have \<open>\<forall>h|\<in>|hashes. \<exists>n|\<in>| (merge G G2). H n = h\<close>
      using extend_graph.hyps(2) by auto
    moreover have \<open>(hashes, val) |\<notin>| (merge G G2)\<close>
      by (simp add: False extend_graph.hyps(3))
    moreover have \<open>H (hashes, val) |\<notin>| hashes\<close>
      by (simp add: extend_graph.hyps(4))
    ultimately show ?thesis
      using struct_valid.extend_graph by presburger
  qed
qed

definition all_values :: \<open>('hash, 'val) hash_graph \<Rightarrow> 'val fset\<close> where
  \<open>all_values G = fimage (\<lambda> (hashes, val). val) G\<close>

subsection \<open>Local New Node\<close>

text \<open>Local new node takes current heads as its predecessors\<close>
lemma local_new_node_not_exist_in_G:
  assumes \<open>struct_valid G\<close>
    and \<open>hs = heads G\<close>
  shows \<open>(hs, v) |\<notin>| G\<close>
using assms proof(induction rule: struct_valid.induct)
  case (empty_graph)
  then show ?case 
    by simp
next
  case (extend_graph G hashes val)
  then show ?case 
    by (metis case_prodD finsert_iff funion_fempty_right funion_finsert_right new_node_in_head 
        old_nodes_not_referencing_new_node prod.inject struct_valid.extend_graph)

qed

lemma local_new_node_not_referencing_itself:
  assumes \<open>struct_valid G\<close>
    and \<open>hs = heads G\<close>
  shows \<open>H (hs, v) |\<notin>| hs\<close>
using assms proof(induction rule: struct_valid.induct)
  case (empty_graph)
  then show ?case
    using empty_heads struct_valid.empty_graph by blast
next
  case (extend_graph G hashes val)
  then show ?case
    by (metis heads_iff local_new_node_not_exist_in_G struct_valid.extend_graph)
qed

lemma local_new_node_is_struct_valid:
  assumes \<open>struct_valid G\<close>
    and \<open>hs = heads G\<close>
  shows \<open>is_struct_valid G (hs, v)\<close>
  by (smt (verit) assms(1) assms(2) fimage_iff head_nodes_iff heads_def is_struct_valid.simps 
      local_new_node_not_exist_in_G local_new_node_not_referencing_itself)


subsection \<open>Local New Node\<close>

lemma local_new_node_preds:
  assumes \<open>hs = heads G\<close>
  shows \<open>head_nodes_set G \<subseteq> preds_of_node (hs, v)\<close>
  using assms head_nodes_def head_nodes_iff head_nodes_set_def heads_iff preds_of_node_def by force

lemma local_new_node_is_head:
  assumes \<open>struct_valid G\<close>
    and \<open>hs = heads G\<close>
  shows \<open>{|(hs, v)|} = head_nodes (G|\<union>|{|(hs, v)|})\<close>
proof -
  have 1: \<open>head_nodes_set (G |\<union>| {|(hs, v)|}) = 
    head_nodes_set G - preds_of_node (hs, v) \<union> {(hs, v)}\<close>
    by (metis assms(1) assms(2) extend_graph hash_graph.head_nodes_update_on_new_node_addition hash_graph_axioms is_struct_valid.simps local_new_node_is_struct_valid)
  have \<open>head_nodes_set G \<subseteq> preds_of_node (hs, v)\<close>
    by (simp add: assms(2) local_new_node_preds)
  then show ?thesis
    by (metis (no_types, lifting) 1 Diff_subset_conv bot_fset.rep_eq finsert_is_funion fset_cong fset_simps(2) head_nodes_def head_nodes_set_def sup_absorb1 sup_bot_right sup_commute)
qed

lemma local_new_node_is_successor_of_all_nodes:
  assumes \<open>struct_valid G\<close>
    and \<open>hs = heads G\<close>
  shows \<open>\<forall>x |\<in>| G. x \<prec> (hs, v)\<close>
proof -
  have \<open>{|(hs, v)|} = head_nodes (G|\<union>|{|(hs, v)|})\<close>
    by (metis assms local_new_node_is_head)
  then have \<open>reachable_nodes_of_set {(hs, v)} = fset (G |\<union>| {| (hs, v) |})\<close>
    by (smt (verit, del_insts) assms(1) assms(2) bot_fset.rep_eq extend_graph fset_simps(2) hash_graph.head_nodes_def hash_graph.head_nodes_set_def hash_graph_axioms is_struct_valid.simps local_new_node_is_struct_valid reachable_nodes_of_heads_is_graph)
  then have \<open>reachable_nodes_of (hs, v) = fset (G|\<union>|{|(hs, v)|})\<close>
    by (simp add: reachable_nodes_of_set_def)
  then have 1: \<open>\<forall>x |\<in>| (G|\<union>|{|(hs, v)|}). x \<preceq> (hs, v)\<close>
    using hash_graph.reachable_nodes_of_def hash_graph_axioms by fastforce
  then have \<open>(hs, v) |\<notin>| G\<close>
    by (simp add: assms(1) assms(2) local_new_node_not_exist_in_G)
  then show ?thesis
    using 1 reachable_def by auto
qed

corollary local_new_node_is_reachable_of_all_nodes:
  assumes \<open>struct_valid G\<close>
    and \<open>hs = heads G\<close>
  shows \<open>\<forall>x |\<in>| (G|\<union>|{|(hs, v)|}). x \<preceq> (hs, v)\<close>
  using assms(1) assms(2) local_new_node_is_successor_of_all_nodes reachable_def by auto

lemma local_new_node_is_not_ancestor_of_any_node:
  assumes \<open>struct_valid G\<close>
    and \<open>hs = heads G\<close>
  shows \<open>\<forall>n |\<in>| G. \<not>((hs, v) \<prec> n)\<close>
  by (metis CollectI assms(1) assms(2) hash_graph.reachable_nodes_of_def hash_graph_axioms 
      local_new_node_not_exist_in_G reachable_def reachable_of_G_node_in_G subset_iff)


end

end