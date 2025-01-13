object BFT_RGA {

def list_all[A](p : A => Boolean, x1 : List[A]) : Boolean = (p, x1) match {
  case (p, Nil) => true
  case (p, x :: xs) => p(x) && list_all[A](p, xs)
}

abstract sealed class set[A]
final case class seta[A](a : List[A]) extends set[A]
final case class coset[A](a : List[A]) extends set[A]

trait equal[A] {
  val `BFT_RGA.equal` : (A, A) => Boolean
}
def equal[A](a : A, b : A)(implicit A: equal[A]) : Boolean =
  A.`BFT_RGA.equal`(a, b)
object equal {
  implicit def `BFT_RGA.equal_integer` : equal[BigInt] = new equal[BigInt] {
    val `BFT_RGA.equal` = (a : BigInt, b : BigInt) => a == b
  }
  implicit def `BFT_RGA.equal_prod`[A : equal, B : equal] : equal[(A, B)] = new
    equal[(A, B)] {
    val `BFT_RGA.equal` = (a : (A, B), b : (A, B)) => equal_proda[A, B](a, b)
  }
  implicit def
    `BFT_RGA.equal_operation`[A : equal, B : equal,
                               C : equal] : equal[operation[A, B, C]]
    = new equal[operation[A, B, C]] {
    val `BFT_RGA.equal` = (a : operation[A, B, C], b : operation[A, B, C]) =>
      equal_operationa[A, B, C](a, b)
  }
  implicit def `BFT_RGA.equal_literal` : equal[String] = new equal[String] {
    val `BFT_RGA.equal` = (a : String, b : String) => a == b
  }
  implicit def `BFT_RGA.equal_fset`[A : equal] : equal[fset[A]] = new
    equal[fset[A]] {
    val `BFT_RGA.equal` = (a : fset[A], b : fset[A]) => equal_fseta[A](a, b)
  }
}

def eq[A : equal](a : A, b : A) : Boolean = equal[A](a, b)

def membera[A : equal](x0 : List[A], y : A) : Boolean = (x0, y) match {
  case (Nil, y) => false
  case (x :: xs, y) => eq[A](x, y) || membera[A](xs, y)
}

def member[A : equal](x : A, xa1 : set[A]) : Boolean = (x, xa1) match {
  case (x, coset(xs)) => ! (membera[A](xs, x))
  case (x, seta(xs)) => membera[A](xs, x)
}

def less_eq_set[A : equal](a : set[A], b : set[A]) : Boolean = (a, b) match {
  case (coset(Nil), seta(Nil)) => false
  case (a, coset(ys)) => list_all[A](((y : A) => ! (member[A](y, a))), ys)
  case (seta(xs), b) => list_all[A](((x : A) => member[A](x, b)), xs)
}

abstract sealed class fset[A]
final case class Abs_fset[A](a : set[A]) extends fset[A]

def fset[A](x0 : fset[A]) : set[A] = x0 match {
  case Abs_fset(x) => x
}

def less_eq_fset[A : equal](xa : fset[A], xc : fset[A]) : Boolean =
  less_eq_set[A](fset[A](xa), fset[A](xc))

def equal_fseta[A : equal](a : fset[A], b : fset[A]) : Boolean =
  less_eq_fset[A](a, b) && less_eq_fset[A](b, a)

trait ord[A] {
  val `BFT_RGA.less_eq` : (A, A) => Boolean
  val `BFT_RGA.less` : (A, A) => Boolean
}
def less_eq[A](a : A, b : A)(implicit A: ord[A]) : Boolean =
  A.`BFT_RGA.less_eq`(a, b)
def less[A](a : A, b : A)(implicit A: ord[A]) : Boolean = A.`BFT_RGA.less`(a, b)
object ord {
  implicit def
    `BFT_RGA.ord_prod`[A : equal : ord, B : equal : ord] : ord[(A, B)] = new
    ord[(A, B)] {
    val `BFT_RGA.less_eq` = (a : (A, B), b : (A, B)) =>
      less_eq_prod[A, B].apply(a).apply(b)
    val `BFT_RGA.less` = (a : (A, B), b : (A, B)) =>
      less_prod[A, B].apply(a).apply(b)
  }
  implicit def `BFT_RGA.ord_literal` : ord[String] = new ord[String] {
    val `BFT_RGA.less_eq` = (a : String, b : String) => a <= b
    val `BFT_RGA.less` = (a : String, b : String) => a < b
  }
}

trait preorder[A] extends ord[A] {
}
object preorder {
  implicit def
    `BFT_RGA.preorder_prod`[A : equal : order,
                             B : equal : order] : preorder[(A, B)]
    = new preorder[(A, B)] {
    val `BFT_RGA.less_eq` = (a : (A, B), b : (A, B)) =>
      less_eq_prod[A, B].apply(a).apply(b)
    val `BFT_RGA.less` = (a : (A, B), b : (A, B)) =>
      less_prod[A, B].apply(a).apply(b)
  }
  implicit def `BFT_RGA.preorder_literal` : preorder[String] = new
    preorder[String] {
    val `BFT_RGA.less_eq` = (a : String, b : String) => a <= b
    val `BFT_RGA.less` = (a : String, b : String) => a < b
  }
}

trait order[A] extends preorder[A] {
}
object order {
  implicit def
    `BFT_RGA.order_prod`[A : equal : order, B : equal : order] : order[(A, B)] =
    new order[(A, B)] {
    val `BFT_RGA.less_eq` = (a : (A, B), b : (A, B)) =>
      less_eq_prod[A, B].apply(a).apply(b)
    val `BFT_RGA.less` = (a : (A, B), b : (A, B)) =>
      less_prod[A, B].apply(a).apply(b)
  }
  implicit def `BFT_RGA.order_literal` : order[String] = new order[String] {
    val `BFT_RGA.less_eq` = (a : String, b : String) => a <= b
    val `BFT_RGA.less` = (a : String, b : String) => a < b
  }
}

trait linorder[A] extends order[A] {
}
object linorder {
  implicit def
    `BFT_RGA.linorder_prod`[A : equal : linorder,
                             B : equal : linorder] : linorder[(A, B)]
    = new linorder[(A, B)] {
    val `BFT_RGA.less_eq` = (a : (A, B), b : (A, B)) =>
      less_eq_prod[A, B].apply(a).apply(b)
    val `BFT_RGA.less` = (a : (A, B), b : (A, B)) =>
      less_prod[A, B].apply(a).apply(b)
  }
  implicit def `BFT_RGA.linorder_literal` : linorder[String] = new
    linorder[String] {
    val `BFT_RGA.less_eq` = (a : String, b : String) => a <= b
    val `BFT_RGA.less` = (a : String, b : String) => a < b
  }
}

def equal_proda[A : equal, B : equal](x0 : (A, B), x1 : (A, B)) : Boolean =
  (x0, x1) match {
  case ((x1, x2), (y1, y2)) => eq[A](x1, y1) && eq[B](x2, y2)
}

def equal_option[A : equal](x0 : Option[A], x1 : Option[A]) : Boolean = (x0, x1)
  match {
  case (None, Some(x2)) => false
  case (Some(x2), None) => false
  case (Some(x2), Some(y2)) => eq[A](x2, y2)
  case (None, None) => true
}

abstract sealed class operation[A, B, C]
final case class Insert[C, A, B](a : C, b : A, c : Option[(A, B)]) extends
  operation[A, B, C]
final case class Delete[A, B, C](a : (A, B)) extends operation[A, B, C]

def equal_operationa[A : equal, B : equal,
                      C : equal](x0 : operation[A, B, C],
                                  x1 : operation[A, B, C]) : Boolean
  =
  (x0, x1) match {
  case (Insert(x11, x12, x13), Delete(x2)) => false
  case (Delete(x2), Insert(x11, x12, x13)) => false
  case (Delete(x2), Delete(y2)) => equal_proda[A, B](x2, y2)
  case (Insert(x11, x12, x13), Insert(y11, y12, y13)) =>
    eq[C](x11, y11) && (eq[A](x12, y12) && equal_option[(A, B)](x13, y13))
}

def rec_prod[A, B, C](f1 : A => B => C, x1 : (A, B)) : C = (f1, x1) match {
  case (f1, (a, b)) => (f1(a))(b)
}

def less_eq_prod[A : equal : ord,
                  B : equal : ord] : ((A, B)) => ((A, B)) => Boolean
  =
  ((x : (A, B)) => (y : (A, B)) =>
    (rec_prod[A, B,
               ((A, B)) =>
                 Boolean](((x_0 : A) => (x_1 : B) => (a : (A, B)) =>
                            {
                              val (y_0, y_1) = a : ((A, B));
                              less[A](x_0, y_0) ||
                                eq[A](x_0, y_0) && less[B](x_1, y_1)
                            }),
                           x)).apply(y) ||
      equal_proda[A, B](x, y))

def less_prod[A : equal : ord, B : ord] : ((A, B)) => ((A, B)) => Boolean =
  ((a : (A, B)) =>
    rec_prod[A, B,
              ((A, B)) =>
                Boolean](((x_0 : A) => (x_1 : B) => (aa : (A, B)) =>
                           {
                             val (y_0, y_1) = aa : ((A, B));
                             less[A](x_0, y_0) ||
                               eq[A](x_0, y_0) && less[B](x_1, y_1)
                           }),
                          a))

def list_ex[A](p : A => Boolean, x1 : List[A]) : Boolean = (p, x1) match {
  case (p, Nil) => false
  case (p, x :: xs) => p(x) || list_ex[A](p, xs)
}

def Bex[A](x0 : set[A], p : A => Boolean) : Boolean = (x0, p) match {
  case (seta(xs), p) => list_ex[A](p, xs)
}

def Ball[A](x0 : set[A], p : A => Boolean) : Boolean = (x0, p) match {
  case (seta(xs), p) => list_all[A](p, xs)
}

def fold[A, B](f : A => B => B, x1 : List[A], s : B) : B = (f, x1, s) match {
  case (f, x :: xs, s) => fold[A, B](f, xs, (f(x))(s))
  case (f, Nil, s) => s
}

def removeAll[A : equal](x : A, xa1 : List[A]) : List[A] = (x, xa1) match {
  case (x, Nil) => Nil
  case (x, y :: xs) =>
    (if (eq[A](x, y)) removeAll[A](x, xs) else y :: removeAll[A](x, xs))
}

def inserta[A : equal](x : A, xs : List[A]) : List[A] =
  (if (membera[A](xs, x)) xs else x :: xs)

def insert[A : equal](x : A, xa1 : set[A]) : set[A] = (x, xa1) match {
  case (x, coset(xs)) => coset[A](removeAll[A](x, xs))
  case (x, seta(xs)) => seta[A](inserta[A](x, xs))
}

def filter[A](p : A => Boolean, x1 : List[A]) : List[A] = (p, x1) match {
  case (p, Nil) => Nil
  case (p, x :: xs) => (if (p(x)) x :: filter[A](p, xs) else filter[A](p, xs))
}

def bind[A, B](x0 : Option[A], f : A => Option[B]) : Option[B] = (x0, f) match {
  case (None, f) => None
  case (Some(x), f) => f(x)
}

def finsert[A : equal](xb : A, xc : fset[A]) : fset[A] =
  Abs_fset[A](insert[A](xb, fset[A](xc)))

def ref_id[A, B, C](x0 : operation[A, B, C]) : Option[A] = x0 match {
  case Insert(v, i, ei) => Some[A](i)
  case Delete(ei) => None
}

def delete[A : equal : linorder,
            B](x0 : List[(A, (B, Boolean))],
                i : A) : Option[List[(A, (B, Boolean))]]
  =
  (x0, i) match {
  case (Nil, i) => None
  case ((ia, (v, flag)) :: xs, i) =>
    (if (eq[A](ia, i)) Some[List[(A, (B, Boolean))]]((ia, (v, true)) :: xs)
      else bind[List[(A, (B, Boolean))],
                 List[(A, (B, Boolean))]](delete[A, B](xs, i),
   ((t : List[(A, (B, Boolean))]) =>
     Some[List[(A, (B, Boolean))]]((ia, (v, flag)) :: t))))
}

def fst[A, B](x0 : (A, B)) : A = x0 match {
  case (x1, x2) => x1
}

def insert_body[A : linorder,
                 B](x0 : List[(A, (B, Boolean))],
                     e : (A, (B, Boolean))) : List[(A, (B, Boolean))]
  =
  (x0, e) match {
  case (Nil, e) => List(e)
  case (x :: xs, e) =>
    (if (less[A](fst[A, (B, Boolean)](x), fst[A, (B, Boolean)](e))) e :: x :: xs
      else x :: insert_body[A, B](xs, e))
}

def insertb[A : equal : linorder,
             B](xs : List[(A, (B, Boolean))], e : (A, (B, Boolean)),
                 x2 : Option[A]) : Option[List[(A, (B, Boolean))]]
  =
  (xs, e, x2) match {
  case (xs, e, None) => Some[List[(A, (B, Boolean))]](insert_body[A, B](xs, e))
  case (Nil, e, Some(i)) => None
  case (x :: xs, e, Some(i)) =>
    (if (eq[A](fst[A, (B, Boolean)](x), i))
      Some[List[(A, (B, Boolean))]](x :: insert_body[A, B](xs, e))
      else bind[List[(A, (B, Boolean))],
                 List[(A, (B, Boolean))]](insertb[A, B](xs, e, Some[A](i)),
   ((t : List[(A, (B, Boolean))]) => Some[List[(A, (B, Boolean))]](x :: t))))
}

def interpret_op[A : equal : linorder, B : equal : linorder,
                  C](h : ((fset[A], operation[B, A, C])) => A,
                      x1 : (fset[A], operation[B, A, C]),
                      xs : List[((B, A),
                                  (C, Boolean))]) : Option[List[((B, A),
                          (C, Boolean))]]
  =
  (h, x1, xs) match {
  case (h, (hs, Insert(v, i, ei)), xs) =>
    {
      val ha = h((hs, Insert[C, B, A](v, i, ei))) : A;
      insertb[(B, A), C](xs, ((i, ha), (v, false)), ei)
    }
  case (h, (hs, Delete(ei)), xs) => delete[(B, A), C](xs, ei)
}

def snd[A, B](x0 : (A, B)) : B = x0 match {
  case (x1, x2) => x2
}

def is_rga_sem_valid[A : equal, B : equal,
                      C](c : ((fset[A], operation[B, A, C])) =>
                               ((fset[A], operation[B, A, C])) => Boolean,
                          h : ((fset[A], operation[B, A, C])) => A,
                          g : set[(fset[A], operation[B, A, C])],
                          x3 : (fset[A], operation[B, A, C])) : Boolean
  =
  (c, h, g, x3) match {
  case (c, h, g, (hs, Insert(v, i, ei))) =>
    (ei match {
       case None => true
       case Some(ii) =>
         Bex[(fset[A],
               operation[B, A,
                          C])](g, ((e : (fset[A], operation[B, A, C])) =>
                                    (c(e))((hs, Insert[C, B, A](v, i, ei))) &&
                                      (eq[A](h(e), snd[B, A](ii)) &&
equal_option[B](ref_id[B, A, C](snd[fset[A], operation[B, A, C]](e)),
                 Some[B](fst[B, A](ii)))))) &&
           ! (eq[A](h((hs, Insert[C, B, A](v, i, ei))), snd[B, A](ii)))
     })
  case (c, h, g, (hs, Delete(ei))) =>
    Bex[(fset[A],
          operation[B, A,
                     C])](g, ((e : (fset[A], operation[B, A, C])) =>
                               (c(e))((hs, Delete[B, A, C](ei))) &&
                                 (eq[A](h(e), snd[B, A](ei)) &&
                                   equal_option[B](ref_id[B, A,
                   C](snd[fset[A], operation[B, A, C]](e)),
            Some[B](fst[B, A](ei))))))
}

def bot_set[A] : set[A] = seta[A](Nil)

def sup_set[A : equal](x0 : set[A], a : set[A]) : set[A] = (x0, a) match {
  case (coset(xs), a) =>
    coset[A](filter[A](((x : A) => ! (member[A](x, a))), xs))
  case (seta(xs), a) =>
    fold[A, set[A]](((aa : A) => (b : set[A]) => insert[A](aa, b)), xs, a)
}

def is_valid[A, B](semF : (fset[(fset[A], B)]) => ((fset[A], B)) => Boolean,
                    strF : (fset[(fset[A], B)]) => ((fset[A], B)) => Boolean,
                    g : fset[(fset[A], B)], x : (fset[A], B)) : Boolean
  =
  (semF(g))(x) && (strF(g))(x)

def is_rga_sem_valid_integer : (((fset[String],
                                  operation[String, String, BigInt])) =>
                                 ((fset[String],
                                   operation[String, String, BigInt])) =>
                                   Boolean) =>
                                 (((fset[String],
                                    operation[String, String, BigInt])) =>
                                   String) =>
                                   (set[(fset[String],
  operation[String, String, BigInt])]) =>
                                     ((fset[String],
                                       operation[String, String, BigInt])) =>
                                       Boolean
  =
  ((a : ((fset[String], operation[String, String, BigInt])) =>
          ((fset[String], operation[String, String, BigInt])) => Boolean)
     =>
    (b : ((fset[String], operation[String, String, BigInt])) => String) =>
    (c : set[(fset[String], operation[String, String, BigInt])]) =>
    (d : (fset[String], operation[String, String, BigInt])) =>
    is_rga_sem_valid[String, String, BigInt](a, b, c, d))

def sup_fset[A : equal](xb : fset[A], xc : fset[A]) : fset[A] =
  Abs_fset[A](sup_set[A](fset[A](xb), fset[A](xc)))

def bot_fset[A] : fset[A] = Abs_fset[A](bot_set[A])

def check_and_apply[A : equal,
                     B : equal](semF : (fset[(fset[A], B)]) =>
 ((fset[A], B)) => Boolean,
                                 strF : (fset[(fset[A], B)]) =>
  ((fset[A], B)) => Boolean,
                                 x2 : (List[(fset[A], B)], fset[(fset[A], B)]),
                                 n : (fset[A],
                                       B)) : (List[(fset[A], B)],
       fset[(fset[A], B)])
  =
  (semF, strF, x2, n) match {
  case (semF, strF, (ah, g), n) =>
    (if (is_valid[A, B](semF, strF, g, n))
      (ah ++ List(n),
        sup_fset[(fset[A],
                   B)](g, finsert[(fset[A], B)](n, bot_fset[(fset[A], B)])))
      else (ah, g))
}

def is_struct_valid[A : equal,
                     B : equal](h : ((fset[A], B)) => A, g : fset[(fset[A], B)],
                                 x2 : (fset[A], B)) : Boolean
  =
  (h, g, x2) match {
  case (h, g, (hashes, vala)) =>
    Ball[A](fset[A](hashes),
             ((ha : A) =>
               Bex[(fset[A],
                     B)](fset[(fset[A], B)](g),
                          ((n : (fset[A], B)) => eq[A](h(n), ha))))) &&
      (! (member[(fset[A], B)]((hashes, vala), fset[(fset[A], B)](g))) &&
        ! (member[A](h((hashes, vala)), fset[A](hashes))))
}

def rga_is_struct_valid : (((fset[String],
                             operation[String, String, BigInt])) =>
                            String) =>
                            (fset[(fset[String],
                                    operation[String, String, BigInt])]) =>
                              ((fset[String],
                                operation[String, String, BigInt])) =>
                                Boolean
  =
  ((a : ((fset[String], operation[String, String, BigInt])) => String) =>
    (b : fset[(fset[String], operation[String, String, BigInt])]) =>
    (c : (fset[String], operation[String, String, BigInt])) =>
    is_struct_valid[String, operation[String, String, BigInt]](a, b, c))

def rga_check_and_apply(c : (fset[(fset[String],
                                    operation[String, String, BigInt])]) =>
                              ((fset[String],
                                operation[String, String, BigInt])) =>
                                ((fset[String],
                                  operation[String, String, BigInt])) =>
                                  Boolean,
                         h : ((fset[String],
                               operation[String, String, BigInt])) =>
                               String) : ((List[(fset[String],
          operation[String, String, BigInt])],
   fset[(fset[String], operation[String, String, BigInt])])) =>
   ((fset[String], operation[String, String, BigInt])) =>
     (List[(fset[String], operation[String, String, BigInt])],
       fset[(fset[String], operation[String, String, BigInt])])
  =
  ((a : (List[(fset[String], operation[String, String, BigInt])],
          fset[(fset[String], operation[String, String, BigInt])]))
     =>
    (b : (fset[String], operation[String, String, BigInt])) =>
    check_and_apply[String,
                     operation[String, String,
                                BigInt]](((g : fset[(fset[String],
              operation[String, String, BigInt])])
    =>
   is_rga_sem_valid_integer.apply(c(g)).apply(h).apply(fset[(fset[String],
                      operation[String, String, BigInt])](g))),
  rga_is_struct_valid.apply(h), a, b))

def interpret_op_integer : (((fset[String],
                              operation[String, String, BigInt])) =>
                             String) =>
                             ((fset[String],
                               operation[String, String, BigInt])) =>
                               (List[((String, String), (BigInt, Boolean))]) =>
                                 Option[List[((String, String),
       (BigInt, Boolean))]]
  =
  ((a : ((fset[String], operation[String, String, BigInt])) => String) =>
    (b : (fset[String], operation[String, String, BigInt])) =>
    (c : List[((String, String), (BigInt, Boolean))]) =>
    interpret_op[String, String, BigInt](a, b, c))

} /* object BFT_RGA */
