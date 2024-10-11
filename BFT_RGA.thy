(* Liangrun Da, Technical University of Munich
   Martin Kleppmann, University of Cambridge
*)
theory
  BFT_RGA
imports
  BFT_Convergence
  "CRDT.Ordered_List"
  "Datatype_Order_Generator.Order_Generator"
begin

section \<open>BFT RGA\<close>

subsection \<open>Definition\<close>

text \<open>
  We now adapt the RGA implementation from Section~\cite{CRDT-AFP} to tolerate Byzantine faults. 
  The ID of each element in RGA affects the position of the element in the list, since 
  $\isa{insert-body}$ skips over the elements that have greater IDs than the inserted element. 
  Therefore, we cannot simply use the hash of the node containing the Insert operation as its ID, 
  as this would prevent the operation generator from controlling the exact position of the inserted 
  element. Instead, we use a pair consisting of an ID that is chosen by the generating peer and the 
  hash of the node containing the Insert operation as the element ID. When comparing element IDs, 
  we first compare the IDs chosen by the peers. If they are identical, we then compare the hashes. 
  This approach ensures that the operation generator can control the position of the inserted element, 
  while still guaranteeing the uniqueness of the ID.
\<close>

type_synonym ('id, 'hash) elem_id = \<open>('id \<times> 'hash)\<close>
derive linorder prod

datatype ('id, 'hash, 'v) operation =
  Insert \<open>'v\<close> \<open>'id\<close> \<open>('id, 'hash) elem_id option\<close> |
  Delete \<open>('id, 'hash) elem_id\<close>

type_synonym ('id, 'hash, 'v) RGAG = \<open>('hash, ('id, 'hash, 'v) operation) hash_graph\<close>
type_synonym ('id, 'hash, 'v) RGAN = \<open>('hash, ('id, 'hash, 'v) operation) node\<close>
type_synonym ('id, 'hash, 'v) RGAH = \<open>('hash, ('id, 'hash, 'v) operation) hash_func\<close>
type_synonym ('id, 'hash, 'v) RGAC = \<open>('hash, ('id, 'hash, 'v) operation) causal_func\<close>

text \<open>
  During the interpretation of the Insert operation, the ID is generated by hashing the node that 
  contains the operation, and combining it with an ID chosen by the generating peer. We did not 
  modify any definitions of the original Ordered-List algorithm~cite{CRDT-AFP}. Instead, we reused 
  it as is, preserving its core functionality while adapting it for our Byzantine fault-tolerant context.
\<close>

fun interpret_op :: \<open>('id::{linorder}, 'hash::{linorder}, 'v) RGAH \<Rightarrow> ('id, 'hash, 'v) RGAN 
  \<Rightarrow> (('id, 'hash) elem_id, 'v) elt list \<rightharpoonup> (('id, 'hash) elem_id, 'v) elt list\<close> where
  \<open>interpret_op H (hs, (Insert v i ei)) xs =
    (let h = H (hs, (Insert v i ei)) in
      insert xs ((i, h), v, True) ei
  )\<close> |
  \<open>interpret_op H (hs, (Delete ei)) xs = delete xs ei\<close>

text \<open>
  This function ensures that:

  \begin{outline}
  \1 For Insert operations:
     \2 The preceding element's ID must exist in the current state.
     \2 The hash node that added the preceding element must be an ancestor of the new node.
     \2 The new node cannot reference itself as an ID (although this is computationally infeasible, we check for it explicitly).
  
  \1 For Delete operations:
     \2 The ID to be deleted must exist in the current state.
     \2 The hash nodes that added the ID must be ancestor of the new node.
  \end{outline}
\<close>

fun is_rga_sem_valid :: \<open>('id, 'hash, 'a) RGAC \<Rightarrow> ('id, 'hash, 'a) RGAH \<Rightarrow> ('id, 'hash, 'a) RGAN set \<Rightarrow> 
  ('id, 'hash, 'a) RGAN \<Rightarrow> bool\<close> where
  \<open>is_rga_sem_valid C H G (hs, Insert v i ei) = (
    case ei of 
      None \<Rightarrow> True
    | Some ii \<Rightarrow> (\<exists>hs' v' i' ei'. 
        (hs', Insert v' i' ei') \<in> G \<and>
        C (hs', Insert v' i' ei') (hs, Insert v i ei) \<and> 
        H (hs', Insert v' i' ei') = snd ii \<and>
        i' = (fst ii)) \<and> 
        H (hs, Insert v i ei) \<noteq> snd ii
  )\<close>
| \<open>is_rga_sem_valid C H G (hs, Delete ei) = (\<exists>hs' v' i' ei'.
    (hs', Insert v' i' ei')  \<in> G \<and>
    C (hs', Insert v' i' ei') (hs, Delete ei) \<and> 
    H (hs', Insert v' i' ei') = snd ei \<and>
    i' = (fst ei)
)\<close>

locale bft_rga = peers_with_arbitrary_history H _ interpret_op \<open>[]\<close> is_rga_sem_valid for
    H :: \<open>('id::{linorder}, 'hash::{linorder}, 'v) RGAH\<close>
begin

notation interp (\<open>\<langle>_\<rangle>\<close> [0] 1000)

subsection \<open>No Failure\<close>

definition indices :: \<open>('id, 'hash, 'v) RGAN list \<Rightarrow> ('id, 'hash) elem_id list\<close> where
  \<open>indices xs \<equiv>
     (List.map_filter (\<lambda>x. case x of 
      (_, Insert v i ei) \<Rightarrow> Some (i, H x)
      | _ \<Rightarrow> None))
  xs\<close>

definition element_ids :: \<open>(('id \<times> 'hash) \<times> 'v \<times> bool) list \<Rightarrow> ('id \<times> 'hash) set\<close> where
 \<open>element_ids list \<equiv> set (map fst list)\<close>

lemma indices_Nil [simp]:
  shows \<open>indices [] = []\<close>
  by(auto simp: indices_def map_filter_def)

lemma indices_append [simp]:
  shows \<open>indices (xs@ys) = indices xs @ indices ys\<close>
  by(auto simp: indices_def map_filter_def)

lemma indices_Deliver_Insert [simp]:
  shows \<open>indices [(hs, Insert v i ei)] = [(i, H (hs, Insert v i ei))]\<close>
  by(auto simp: indices_def map_filter_def)

lemma indices_Deliver_Delete [simp]:
  shows \<open>indices [(hs, Delete i)] = []\<close>
  by(auto simp: indices_def map_filter_def)

lemma idx_in_elem_inserted [intro]:
  assumes \<open>(hs, Insert v i ei) \<in> set xs\<close>
  shows   \<open>(i, H (hs, Insert v i ei)) \<in> set (indices xs)\<close>
  using assms by (induction xs, auto simp add: indices_def map_filter_def)

lemma apply_op_idx_elems:
  assumes \<open>check_and_apply (dn, G) n = (dn', G')\<close>
    and \<open>apply_operations dn = Some es\<close>
    and \<open>element_ids es = set (indices dn)\<close>
    and \<open>apply_operations dn' = Some es'\<close>
  shows \<open>element_ids es' = set (indices dn')\<close>
proof (cases \<open>is_valid G n\<close>)
  case True
  have es'_es: \<open>Some es' = interp n es\<close>
    using True assms(1) assms(2) assms(4) by auto
  then show ?thesis proof (cases \<open>snd n\<close>)
    case (Insert v i ei)
    obtain h where "h = H n"
      by blast
    then have \<open>Some es' = insert es ((i, h), v, True) ei\<close>
      by (metis Insert es'_es interp.elims interpret_op.simps(1) prod.collapse)
    then have 1: \<open>element_ids es' = element_ids es \<union> {(i, h)}\<close>
      using insert_preserve_indices'
      by (metis element_ids_def fst_conv list.set_map option.sel) 
    then have \<open>set (indices dn') = set (indices dn) \<union> {(i, h)}\<close>
      by (metis (no_types, lifting) Insert True \<open>h = H n\<close> assms(1) bft_rga.indices_append 
          bft_rga_axioms check_and_apply.simps fst_conv indices_Deliver_Insert list.set(1) 
          list.simps(15) prod.collapse set_append)
    then show ?thesis
      using "1" assms(3) by argo
  next
    case (Delete x2)
    have \<open>Some es' = delete es x2\<close>
      by (metis Delete es'_es interp.elims interpret_op.simps(2) prod.collapse)
    then have 1: \<open>element_ids es' = element_ids es\<close>
      by (metis delete_preserve_indices element_ids_def list.set_map)
    then have \<open>set (indices dn') = set (indices dn)\<close>
      by (metis Delete append_self_conv assms(1) check_and_apply.simps indices_Deliver_Delete indices_append prod.exhaust_sel prod.inject)
    then show ?thesis
      using 1 assms(3) by blast
  qed
next
  case False
  then show ?thesis
    using assms(1) assms(2) assms(3) assms(4) by force
qed

lemma apply_opers_idx_elems:
  assumes \<open>apply_history (dn, G) ns = (dn', G')\<close>
      and \<open>apply_operations dn = Some es\<close>
      and \<open>element_ids es = set (indices dn)\<close>
      and \<open>apply_operations dn' = Some es'\<close>
    shows \<open>element_ids es' = set (indices dn')\<close>
using assms proof(induction ns arbitrary: dn' G' es' rule:rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs)
  obtain dn'' G'' where dn_G''_d: "apply_history (dn, G) xs = (dn'', G'')"
    by fastforce
  have 1: \<open>check_and_apply (dn'', G'') x = (dn', G')\<close>
    using dn_G''_d snoc.prems(1) by force
  obtain es'' where 2: \<open>apply_operations dn'' = Some es''\<close>
    by (metis 1 apply_operations_Some check_and_apply.simps fst_conv snoc.prems(4))
  then have \<open>element_ids es'' = set (indices dn'')\<close>
    using snoc(1)[of \<open>dn''\<close> \<open>G''\<close> \<open>es''\<close>] dn_G''_d snoc.prems(2) snoc.prems(3) by fastforce
  then show ?case
    using "1" 2 apply_op_idx_elems snoc.prems(4) by blast
qed

lemma step_never_fails_with_idx_elems:
  assumes \<open>check_and_apply (dn, G) (hs, v) = (dn', G')\<close>
     and \<open>fset_of_list dn = G\<close>
     and \<open>apply_operations dn = Some es\<close>
     and \<open>element_ids es = set (indices dn)\<close>
   shows \<open>no_failure dn'\<close>
proof (cases \<open>is_valid G (hs, v)\<close>)
  case True
  have dn'_d: \<open>dn' = dn @ [(hs, v)]\<close>
    using True assms(1) by auto
  have \<open>hb.apply_operations dn' [] =  \<langle>(hs, v)\<rangle> es\<close>
    using dn'_d apply_operations_def apply_operations_snoc assms by presburger
  moreover have \<open>\<langle>(hs, v)\<rangle> es \<noteq> None\<close>
  proof (cases \<open>v\<close>)
    case (Insert x11 x12 x13)
    obtain h where "h = H (hs, v)"
      by blast
    have insert_unfold: \<open>\<langle>(hs, v)\<rangle> es = insert es ((x12, h), x11, True) x13\<close>
      by (simp add: Insert \<open>h = H (hs, v)\<close>)
    then show ?thesis proof (cases \<open>x13\<close>)
      case None
      then show ?thesis
        using insert_unfold by auto
    next
      case (Some a)
      have \<open>is_sem_valid G (hs, Insert x11 x12 x13)\<close>
        using Insert True is_valid.elims(2) by blast
      then have \<open>is_rga_sem_valid (\<prec>) H (fset G) (hs, Insert x11 x12 (Some a))\<close>
        using Some is_sem_valid.simps by blast
      then have \<open>\<exists>hs' v' i' ei'. 
        (hs', Insert v' i' ei') \<in> (fset G) \<and>
        H (hs', Insert v' i' ei') = snd a \<and>
        i' = (fst a)\<close>
        by (simp split: option.splits) blast
      then have \<open>a \<in> set (indices dn)\<close>
        by (metis assms(2) fset_of_list.rep_eq idx_in_elem_inserted prod.exhaust_sel)
      then show ?thesis
        by (metis Some assms(4) element_ids_def insert_Some_None_index_not_in insert_unfold list.set_map)
    qed
  next
    case (Delete x2)
    have 1: \<open>\<langle>(hs, v)\<rangle> es = delete es x2\<close>
      by (metis Delete interp.elims interpret_op.simps(2))
    have \<open>is_sem_valid G (hs, Delete x2)\<close>
      using Delete True by simp
    then have \<open>x2 \<in> set (indices dn)\<close>
      using assms(2) fset_of_list.rep_eq idx_in_elem_inserted by fastforce
    then show ?thesis
      by (metis 1 assms(4) delete_None_index_not_in element_ids_def list.set_map)
  qed
  ultimately show ?thesis
    using no_failure_def by auto
next
  case False
  have \<open>no_failure dn\<close>
    using apply_operations_def assms(3) no_failure_def by force
  then show ?thesis
    by (metis False assms(1) check_and_apply.simps fst_eqD)
qed

lemma step_never_fails:
  assumes \<open>apply_history ([], {||}) ns = (dn, G)\<close>
     and \<open>no_failure dn\<close>
     and \<open>check_and_apply (dn, G) (hs, v) = (dn', G')\<close>
   shows \<open>no_failure dn'\<close>
proof -
  have 1: \<open>fset_of_list dn = G\<close>
    by (meson assms(1) peer_apply_history_preserve_same_nodes)
  obtain es where 2: \<open>apply_operations dn = Some es\<close>
    using apply_operations_def assms(2) no_failure_def by auto
  have \<open>element_ids es = set (indices dn)\<close>
    using \<open>apply_operations dn = Some es\<close> apply_operations_def apply_opers_idx_elems assms(1) element_ids_def by force
  then show ?thesis
    using 1 2 assms(3) step_never_fails_with_idx_elems by blast
qed

subsection \<open>Concurrent Operations Commute\<close>

lemma same_insert:
  assumes \<open>H (hs1, Insert v1 i1 ei1) = H (hs2, Insert v2 i2 ei2)\<close>
  shows \<open>Insert v1 i1 ei1 = Insert v2 i2 ei2\<close>
  using assms hash_no_collisions by blast

lemma insert_has_pred_id:
  assumes \<open>valid_graph G\<close>
    and \<open>x |\<in>| G\<close>
    and \<open>x = (hs, Insert v i (Some ei))\<close>
  shows \<open>\<exists>y |\<in>| G. y \<prec> x \<and> H y = snd ei\<close>
using assms proof(induction arbitrary: x rule: valid_graph.induct)
  case 1
  then show ?case 
    by blast
next
  case (2 G n)
  then show ?case
    by auto
qed

lemma delete_has_pred_id:
  assumes \<open>valid_graph G\<close>
    and \<open>x |\<in>| G\<close>
    and \<open>x = (hs, Delete ei)\<close>
  shows \<open>\<exists>y |\<in>| G. y \<prec> x \<and> H y = snd ei\<close>
using assms proof(induction arbitrary: x rule: valid_graph.induct)
  case 1
  then show ?case 
    by blast
next
  case (2 G n)
  then show ?case
    by auto
qed

lemma insert_commute_id: 
  assumes \<open>valid_graph G\<close>
    and \<open>x = (hs1, Insert v1 i1 ei1)\<close>
    and \<open>y = (hs2, Insert v2 i2 ei2)\<close>
    and \<open>x |\<in>| G\<close>
    and \<open>y |\<in>| G\<close>
    and \<open>hb.concurrent x y\<close>
  shows \<open>ei2 = None \<or> ei2 \<noteq> Some (h, H x)\<close>
using assms proof(induction arbitrary: x y rule: valid_graph.induct)
  case 1
  then show ?case 
    by fastforce
next
  case (2 G n)
  then show ?case proof (cases \<open>snd n\<close>)
    case (Insert x11 x12)
    then show ?thesis apply (cases \<open>x |\<in>| G\<close>; cases \<open>y |\<in>| G\<close>)
      using "2.IH" "2.prems"(1) "2.prems"(2) "2.prems"(5) apply blast
      apply (metis "2.prems"(1) assms(1) assms(2) assms(3) assms(5) assms(6) bft_rga.insert_has_pred_id bft_rga_axioms hash_graph_axioms hash_graph_def hb.concurrentD1 snd_eqD)
      apply (metis "2.hyps"(1) "2.prems"(2) hash_no_collisions insert_has_pred_id snd_conv)
      by (metis "2.prems"(1) assms(1) assms(2) assms(3) assms(5) assms(6) hash_no_collisions hb.concurrentD1 insert_has_pred_id snd_conv)
  next
    case (Delete x2)
    then show ?thesis apply (cases \<open>x |\<in>| G\<close>; cases \<open>y |\<in>| G\<close>)
      using "2.IH" "2.prems" by force+
  qed
qed

lemma ins_del_commute_id:
  assumes \<open>valid_graph G\<close>
    and \<open>x = (hs1, Insert v1 i1 ei1)\<close>
    and \<open>y = (hs2, Delete ei2)\<close>
    and \<open>x |\<in>| G\<close>
    and \<open>y |\<in>| G\<close>
    and \<open>hb.concurrent x y\<close>
  shows \<open>snd ei2 \<noteq> H x\<close>
using assms proof(induction arbitrary: x y rule: valid_graph.induct)
  case 1
  then show ?case 
    by fastforce
next
  case (2 G n)
  then show ?case proof (cases \<open>snd n\<close>)
    case (Insert x11 x12)
    then show ?thesis apply (cases \<open>x |\<in>| G\<close>; cases \<open>y |\<in>| G\<close>)
      defer 3
      using "2.IH" "2.prems" apply force+
      by (metis "2.hyps"(1) "2.prems"(2) delete_has_pred_id hash_no_collisions)
  next
    case (Delete x2)
    then show ?thesis apply (cases \<open>x |\<in>| G\<close>; cases \<open>y |\<in>| G\<close>)
      defer 2
      using "2.IH" "2.prems" apply force+
      by (metis "2.prems"(1) assms(1) assms(2) assms(3) assms(5) assms(6) 
          delete_has_pred_id hash_no_collisions hb.concurrentD1)
  qed
qed

text \<open>Del Del operations commute\<close>

lemma del_del_commute:
  shows \<open>\<langle>(hs1, Delete ei1)\<rangle> \<rhd> \<langle>(hs2, Delete ei2)\<rangle> = \<langle>(hs2, Delete ei2)\<rangle> \<rhd> \<langle>(hs1, Delete ei1)\<rangle>\<close>
proof -
  have \<open>\<forall>ii. delete ii ei1 \<bind> (\<lambda>x. delete x ei2) = delete ii ei2 \<bind> (\<lambda>x. delete x ei1)\<close>
    using delete_commutes by blast
  then show ?thesis
    by (clarsimp simp add: kleisli_def; blast)
qed

lemma ins_ins_commute:
  assumes "valid_graph G"
    and \<open>x = (hs1, Insert v1 i1 ei1)\<close>
    and \<open>y = (hs2, Insert v2 i2 ei2)\<close>
    and \<open>x |\<in>| G\<close>
    and \<open>y |\<in>| G\<close>
    and \<open>hb.concurrent x y\<close>
  shows \<open>\<langle>x\<rangle> \<rhd> \<langle>y\<rangle> = \<langle>y\<rangle> \<rhd> \<langle>x\<rangle>\<close>
proof -
  have 1: \<open>ei2 = None \<or> ei2 \<noteq> Some (i1, H x)\<close>
    using assms insert_commute_id by auto
  have 2: \<open>ei1 = None \<or> ei1 \<noteq> Some (i2, H y)\<close>
    using assms hb.concurrent_comm insert_commute_id by auto
  have \<open>\<forall>ii. insert ii ((i1, H x), v1, True) ei1 
    \<bind> (\<lambda>e. insert e ((i2, H y), v2, True) ei2) = 
    insert ii ((i2, H y), v2, True) ei2 
    \<bind> (\<lambda>e. insert e ((i1, H x), v1, True) ei1)\<close>
    using insert_commutes
    by (metis "1" "2" Pair_inject assms(2) assms(3) fstI hash_no_collisions operation.inject(1) option.distinct(1))
  then show ?thesis 
    apply (clarsimp simp add: kleisli_def)
    using assms(2) assms(3) by auto
qed

lemma ins_del_commute:
  assumes "valid_graph G"
    and \<open>x = (hs1, Insert v1 i1 ei1)\<close>
    and \<open>y = (hs2, Delete ei2)\<close>
    and \<open>x |\<in>| G\<close>
    and \<open>y |\<in>| G\<close>
    and \<open>hb.concurrent x y\<close>
  shows \<open>\<langle>x\<rangle> \<rhd> \<langle>y\<rangle> = \<langle>y\<rangle> \<rhd> \<langle>x\<rangle>\<close>
proof -
  have "snd ei2 \<noteq> H (hs1, Insert v1 i1 ei1)"
    using assms ins_del_commute_id by blast
  then have \<open>\<forall>ii. insert ii ((i1, H x), v1, True) ei1 \<bind> (\<lambda>e. delete e ei2) = 
    delete ii ei2 \<bind> (\<lambda>e. insert e ((i1, H x), v1, True) ei1)\<close>
    by (metis assms(2) fstI insert_delete_commute snd_conv)
  then show ?thesis 
    apply (clarsimp simp add: kleisli_def) 
    using assms(2) assms(3) by auto
qed

lemma concurrent_operations_commute:
  assumes \<open>xs = (delivered_nodes i)\<close>
  shows \<open>hb.concurrent_ops_commute xs\<close>
proof -
  have \<open>\<And>x y. {x, y} \<subseteq> set xs \<Longrightarrow> hb.concurrent x y \<Longrightarrow> \<langle>x\<rangle> \<rhd> \<langle>y\<rangle> =  \<langle>y\<rangle> \<rhd> \<langle>x\<rangle>\<close>
  proof
    fix x y ii
    assume \<open>{x, y} \<subseteq> set xs\<close>
      and C: \<open>hb.concurrent x y\<close>
    hence X: \<open>x \<in> set xs\<close> and Y: \<open>y \<in> set xs\<close>
      by auto
    obtain hsx hsy vx vy where 1: \<open>x = (hsx, vx)\<close> and 2: \<open>y = (hsy, vy)\<close>
      by fastforce
    have valid_G: \<open>valid_graph (graph i)\<close>
      by (metis apply_history_preserve_validity local.graph_def peer_state.elims prod.collapse valid_graph.intros(1))
    have xyG: \<open>x |\<in>| (graph i) \<and> y |\<in>| (graph i)\<close>
      using X Y assms in_history_in_graph by blast
    thus \<open>(\<langle>x\<rangle> \<rhd> \<langle>y\<rangle>) ii = (\<langle>y\<rangle> \<rhd> \<langle>x\<rangle>) ii\<close>
      apply (cases vx; cases vy)
      using "1" "2" C ins_ins_commute apply (metis valid_G)
      using "1" "2" C ins_del_commute valid_G apply auto[1]
      using "1" "2" C hb.concurrent_comm ins_del_commute valid_G xyG apply presburger
      using "1" "2" del_del_commute by presburger
  qed
  thus \<open>hb.concurrent_ops_commute (xs)\<close>
    by(auto simp add: hb.concurrent_ops_commute_def)
qed

subsection \<open>Synchronization\<close>

lemma sem_valid_only_ancestors_relevant: 
  assumes \<open>(ancestor_nodes_of n) \<subseteq> fset G\<close>
  shows \<open>is_sem_valid_set (ancestor_nodes_of n) n \<longleftrightarrow> is_sem_valid G n\<close>
proof
  assume \<open>is_sem_valid_set (ancestor_nodes_of n) n\<close>
  show \<open>is_sem_valid G n\<close>
  proof (cases \<open>snd n\<close>)
    case (Insert v i ei)
    obtain hs where n_d: \<open>n = (hs, (Insert v i ei))\<close>
      by (metis Insert eq_snd_iff)
    then show ?thesis proof (cases ei)
      case None
      then show ?thesis 
        by (simp add: None n_d)
    next
      case (Some a)
      then show ?thesis
        using \<open>is_sem_valid_set (ancestor_nodes_of n) n\<close> assms n_d by auto
    qed
  next
    case (Delete i)
    obtain hs where n_d: \<open>n = (hs, (Delete i))\<close>
      by (metis Delete prod.collapse)
    then show ?thesis
      using \<open>is_sem_valid_set (ancestor_nodes_of n) n\<close> assms by auto
  qed
next
  assume \<open>is_sem_valid G n\<close> 
  show \<open>is_sem_valid_set (ancestor_nodes_of n) n\<close> proof (cases \<open>snd n\<close>)
    case (Insert v i ei)
    obtain hs where n_d: \<open>n = (hs, (Insert v i ei))\<close>
      by (metis Insert eq_snd_iff)
    then show ?thesis proof (cases \<open>ei\<close>)
      case None
      then show ?thesis
        by (simp add: n_d)
    next
      case (Some a)
      then show ?thesis
        using \<open>is_sem_valid G n\<close> ancestor_nodes_of_def n_d by auto
    qed
  next
    case (Delete i)
    obtain hs where n_d: \<open>n = (hs, (Delete i))\<close>
      by (metis Delete prod.collapse)
    then show ?thesis
      using \<open>is_sem_valid G n\<close> ancestor_nodes_of_def by fastforce
  qed    
qed

sublocale sec: bft_strong_eventual_consistency H _ interpret_op \<open>[]\<close> is_rga_sem_valid
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

thm sec.sec_convergence

end

end
