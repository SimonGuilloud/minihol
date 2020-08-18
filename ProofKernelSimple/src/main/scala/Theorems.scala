import Core._
import stainless.lang.{print =>pprint, _}
import stainless.collection._
import stainless.annotation._
import stainless.math._
import stainless.proof._

object Theorems {

  /////////////////////////////
  //Useful Lemmas
  /////////////////////////////
  @opaque
  def equalUnConstruct(thm: Theorem):Unit = {
    require(thm.isWellConstructed)

    thm.f match {
      case Application(Application(Constant("=", Func(a, Func(b, Bool)), param_types), l), r) =>
        val cEq = Constant("=", Func(a, Func(b, Bool)), param_types)
        assert(cEq.isWellConstructed)
        assert(a == b)
        assert(Application(cEq, l).isWellConstructed && l.typ == a)
        assert(Application(Application(cEq, l), r).isWellConstructed)
        assert(r.typ == Application(cEq, l).typ.in)
        assert(r.typ == Func(a, Func(b, Bool)).out.in)
        assert(r.typ == b)
        check(a == b && l.typ == b && r.typ == a && l.typ == r.typ && l.isWellConstructed && r.isWellConstructed)
        ()
      case _ => ()
    }
  }.ensuring(_ => thm.isWellConstructed ==> (thm.f match {
    case Application(Application(Constant("=", Func(a, Func(b, Bool)), param_types), l), r) => a==b && l.typ == b && r.typ == a && l.typ == r.typ && l.isWellConstructed && r.isWellConstructed
    case _ => true
  }))
  @opaque
  def forallUnion[T](@induct l1: List[T], l2: List[T], p: T => Boolean): Unit ={
    require(l1.forall(p) && l2.forall(p))
  }.ensuring(_ => (l1++l2).forall(p))
  @opaque
  def forallUnionCdef(@induct l1: List[ConstantDefinition], l2: List[ConstantDefinition]): Unit ={
    require(l1.forall(_.isWellConstructed) && l2.forall(_.isWellConstructed))
  }.ensuring(_ => (l1++l2).forall(_.isWellConstructed))
  @opaque
  def forallRemove[T](@induct l1: List[T], l2: List[T], p: T => Boolean): Unit ={
  }.ensuring(_ => l1.forall(p) ==> (l1--l2).forall(p))
  @opaque
  def substOK(t:Term, x1:Variable, t1:Term):Unit ={
    require(t.isWellConstructed && x1.isWellConstructed && t1.isWellConstructed && t.substitutionPossible(x1, t1))
  }.ensuring(_ => t.substitute(x1, t1).isWellConstructed)
  @opaque
  def forallHead[T](li:List[T], p:T=>Boolean): Unit ={
    require(!li.isEmpty && li.forall(p))
    if (!li.tail.isEmpty){
      forallHead(li.tail, p)
    }
  }.ensuring(_ => p(li.head) && li.tail.forall(p))
  @opaque
  def forallAnd[T](@induct li:List[T], p:T=>Boolean, q:T=>Boolean): Unit ={
    require(li.forall(p) && li.forall(q))
  }.ensuring(_ => li.forall(r => p(r) && q(r) ))
  @opaque
  def forallTrue[T](@induct li:List[T], p: Boolean): Unit ={
  }.ensuring(_ => p ==> li.forall(t => p))

  def map[T, U](li: List[T], f:T=>U, p:T=>Boolean, q: U=>Boolean): List[U] ={
    require(li.forall(p) && li.forall(r => p(r) ==> q(f(r)) ))
    if (li.isEmpty) Nil[U]()
    else {
      forallHead(li, p)
      assert(p(li.head))
      val h = List(f(li.head))
      val ta = map(li.tail, f, p, q)
      assert(h.forall(q))
      assert(ta.forall(q))
      forallUnion[U](h, ta, q)
      check((h++ta).forall(q))
      h++ta
    }
  }.ensuring(_.forall(q))

  def mapSubst(@induct li: List[Term], x1: Variable, t1:Term): List[Term] ={
    require(li.forall(_.substitutionPossible(x1, t1)) && x1.isWellConstructed && t1.isWellConstructed && x1.typ == t1.typ)
    if (li.isEmpty) Nil[Term]()
    else {
      forallHead[Term](li, _.substitutionPossible(x1, t1))
      assert(li.head.substitutionPossible(x1, t1))
      val h = List(li.head.substitute(x1, t1))
      val ta = mapSubst(li.tail, x1, t1)
      assert(li.head.substitute(x1, t1).isWellConstructed)
      assert(h.forall(_.isWellConstructed))
      assert(ta.forall(_.isWellConstructed))
      forallUnion[Term](h, ta, _.isWellConstructed)
      check((h ++ ta).forall(_.isWellConstructed))
      h ++ ta
    }
  }.ensuring(r => r.forall(_.isWellConstructed))
  @opaque
  def mapSubstType(@induct li: List[Term], alpha1: TypeVariable, tau1:HOL_type): List[Term] ={
    require(li.forall(_.isWellConstructed) && alpha1.isWellConstructed && tau1.isWellConstructed && tau1!=Unit)
    if (li.isEmpty) Nil[Term]()
    else {
      forallHead[Term](li, _.isWellConstructed)
      assert(li.head.isWellConstructed)
      val h = List(li.head.substituteType(alpha1, tau1))
      val ta = mapSubstType(li.tail, alpha1, tau1)
      assert(li.head.substituteType(alpha1, tau1).isWellConstructed)
      assert(h.forall(_.isWellConstructed))
      assert(ta.forall(_.isWellConstructed))
      forallUnion[Term](h, ta, _.isWellConstructed)
      check((h ++ ta).forall(_.isWellConstructed))
      h ++ ta
    }
  }.ensuring(r => r.forall(_.isWellConstructed))
  /////////////////////////////
  //End of Lemmas
  /////////////////////////////


  case class ConstantDefinition(c: Constant, t: Term) {
    def isWellConstructed: Boolean = t.isWellConstructed && c.isWellConstructed
    def substituteType2(alpha1: TypeVariable, tau1: HOL_type): ConstantDefinition = {
      require(tau1 != Unit && this.isWellConstructed && alpha1.isWellConstructed && tau1.isWellConstructed)
      val nc = c.substituteType(alpha1, tau1)
      assert(nc.isInstanceOf[Constant])
      ConstantDefinition(nc.asInstanceOf[Constant], t.substituteType(alpha1, tau1))
    }
    def conflicts(that: ConstantDefinition): Boolean = this.c.name == that.c.name && this.t != that.t
  }

  case class TypeDefinition(ct: CustomType, bt: HOL_type, predicate: Term){
    def isWellConstructed: Boolean = bt.isWellConstructed &&
      predicate.isWellConstructed &&
      predicate.typ == Func(bt, Bool)
    def conflicts(that:TypeDefinition): Boolean = this.ct.name == that.ct.name && this != that
  }


  //Defines the conservative extension in which a theorem is expressed. Contains all definitions of constants.
  type ConsEnvironment = List[ConstantDefinition]
  val basicConsEnvironment: ConsEnvironment = List(ConstantDefinition(equal, equal))
  def findConflictsCons(env1: ConsEnvironment, env2: ConsEnvironment) : List[ConstantDefinition] = {
    val unicd = env1  ++ env2
    unicd.filter(cd1 => unicd.exists(cd2 => cd1 conflicts cd2))
  }
  def areCompatibleCons(env1: ConsEnvironment, env2: ConsEnvironment): Boolean = {
    val uni = env1 ++ env2
    val p = (cd1:ConstantDefinition) => uni.exists(cd2 => cd1 conflicts cd2)
    filterEmpty[ConstantDefinition](uni, p)
    !uni.exists(cd1 => uni.exists(cd2 => cd1 conflicts cd2) )
  }.ensuring(r => r == findConflictsCons(env1, env2).isEmpty) //help stainless

  type TypesEnvironment = List[TypeDefinition]
  val basicTypesEnvironment: TypesEnvironment = List()
  def findConflictsTypes(env1: TypesEnvironment, env2: TypesEnvironment) : List[TypeDefinition] = {
    val unitd = env1  ++ env2
    unitd.filter(td1 => unitd.exists(td2 => td1 conflicts td2))
  }
  def areCompatibleTypes(env1: TypesEnvironment, env2: TypesEnvironment): Boolean = {
    val uni = env1 ++ env2
    val p = (cd1:TypeDefinition) => uni.exists(cd2 => cd1 conflicts cd2)
    filterEmpty[TypeDefinition](uni, p)
    !uni.exists(cd1 => uni.exists(cd2 => cd1 conflicts cd2) )
  }.ensuring(r => r == findConflictsTypes(env1, env2).isEmpty) //help stainless

  //Define the Assumptions of a theorem, i.e. the left hand side of the sequent
  type Assumptions = List[Term]
  val basicAssumptions: Assumptions = List()

  //Define Theorems, with a private constructor so that a theorem can only be created using the following inference rules.
  case class Theorem private (f: Term, c: Assumptions, cEnv: ConsEnvironment, tEnv: TypesEnvironment) {
    def isWellConstructed: Boolean = f.isWellConstructed && f.typ == Bool &&
      c.forall(_.isWellConstructed) && cEnv.forall(_.isWellConstructed) && cEnv.forall(_.isWellConstructed) && tEnv.forall(_.isWellConstructed)
  }


  // -----------------------------------
  // Here starts the 11 rules of inference that make the core of the deduction system.
  //------------------------------------

  //---------------Stainless is ok until here

  //Equality is reflexive
  //
  // |- t=t
  def REFL(t: Term):Theorem  = {
    require(t.isWellConstructed)
    Theorem(safe_equal(t,t), basicAssumptions, basicConsEnvironment, basicTypesEnvironment)
  }.ensuring(_.isWellConstructed)

  //Equality is transitive
  // |-s=t  |-t=u
  //    |-s=u
  def _TRANS(first: Theorem, second: Theorem): Theorem = {
    require(
      ((first.f, second.f) match {
        case (Application(Application(Constant("=", Func(a, Func(b, Bool)), _), s), t), Application(Application(Constant("=", Func(c, Func(d, Bool)), _), u), v)) => t == u
        case _ => false
      }) &&
        areCompatibleCons(first.cEnv, second.cEnv) && areCompatibleTypes(first.tEnv, second.tEnv) && first.isWellConstructed && second.isWellConstructed
    )
    (first.f, second.f) match { //safe_equal precondition
      case (Application(Application(Constant("=", Func(a, Func(b, Bool)), _), s), t), Application(Application(Constant("=", Func(c, Func(d, Bool)), _), u), v)) =>
        assert(first.f.isWellConstructed && second.f.isWellConstructed)
        equalUnConstruct(first)
        equalUnConstruct(second)
        assert(s.typ == t.typ)
        assert(t.typ == u.typ)
        assert(u.typ == v.typ)
        forallUnion[Term](first.c, second.c, te => te.isWellConstructed)
        assert((first.c ++ second.c).forall(_.isWellConstructed))
        forallUnion[ConstantDefinition](first.cEnv, second.cEnv, defi => defi.isWellConstructed)
        assert((first.cEnv ++ second.cEnv).forall(_.isWellConstructed))
        forallUnion[TypeDefinition](first.tEnv, second.tEnv, defi => defi.isWellConstructed)
        assert((first.tEnv ++ second.tEnv).forall(_.isWellConstructed))
        val r = Theorem(safe_equal(s,v), (first.c ++ second.c), (first.cEnv ++ second.cEnv), (first.tEnv ++ second.tEnv))
        check(r.isWellConstructed)
        r
    }
  }.ensuring(_.isWellConstructed)

  //Congruence property of equality
  //  |-s=t  |u=v
  //  |-s(u)=t(v)
  //  Types need to match
  def MK_COMB(first: Theorem, second:Theorem): Theorem = {
    require( first.isWellConstructed && second.isWellConstructed &&
      ((first.f, second.f) match {
        case (Application(Application(Constant("=", Func(a, Func(b, Bool)), _), s), t), Application(Application(Constant("=", Func(c, Func(d, Bool)), _), u), v)) => s.typ.in == u.typ && t.typ.in == v.typ
        case _ => false
      }) && areCompatibleCons(first.cEnv, second.cEnv) && areCompatibleTypes(first.tEnv, second.tEnv))
    (first.f, second.f) match {
      case (Application(Application(Constant("=", Func(a, Func(b, Bool)), _), s), t), Application(Application(Constant("=", Func(c, Func(d, Bool)), _), u), v)) =>
        assert(first.f.isWellConstructed && second.f.isWellConstructed)
        equalUnConstruct(first)
        equalUnConstruct(second)
        assert(s.typ == t.typ)
        assert(u.typ == v.typ)
        forallUnion[ConstantDefinition](first.cEnv, second.cEnv, defi => defi.isWellConstructed)
        forallUnion[TypeDefinition](first.tEnv, second.tEnv, defi => defi.isWellConstructed)
        forallUnion[Term](first.c, second.c, te => te.isWellConstructed)
        assert(Application(s, u).isWellConstructed && Application(t, v).isWellConstructed)
        val r = Theorem(safe_equal(Application(s, u), Application(t, v)), (first.c ++ second.c), (first.cEnv ++ second.cEnv), (first.tEnv ++ second.tEnv)) // precond for safe_equal, adt for theorem, adt for application t, v
        check(r.isWellConstructed)
        r
    }
  }.ensuring(_.isWellConstructed)


  //Abstraction rule
  //      |-s=t
  //  |-\x. s = \x.t
  def ABS(eq: Theorem, x: Variable): Theorem = {
    require((eq.f match {
      case Application(Application(Constant("=", Func(a, Func(b, Bool)), param_types), l), r) => true
      case _ => false
    }) && !eq.c.exists(t => t.freeVariables.contains(x))  && eq.isWellConstructed && x.isWellConstructed )
    eq.f match {
      case Application(Application(Constant("=", Func(a, Func(b, Bool)), param_types), l), r) =>
        equalUnConstruct(eq)
        assert(a==b)
        assert(l.typ == r.typ)
        assert(Abstraction(x, l).typ == Func(x.typ, l.typ))
        assert(Abstraction(x, r).typ == Func(x.typ, r.typ))
        assert(Abstraction(x, l).typ == Abstraction(x, r).typ)
        assert(Abstraction(x, l).isWellConstructed)
        assert(Abstraction(x, r).isWellConstructed)
        Theorem(safe_equal(Abstraction(x, l), Abstraction(x, r)), eq.c, eq.cEnv, eq.tEnv)
    }
  }.ensuring(_.isWellConstructed)

  //Beta-conversion of lambda calculus, i.e Application of Abstraction does nothing
  //
  //  |- (\x. t)(x)=t
  def BETA(x : Variable, t: Term): Theorem = {
    require(x.isWellConstructed && t.isWellConstructed)
    assert(Application(Abstraction(x, t), x).typ == t.typ)
    assert(Application(Abstraction(x, t), x).isWellConstructed)
    assert(basicAssumptions.forall(_.isWellConstructed))
    assert(basicConsEnvironment.forall(_.isWellConstructed))
    assert(basicTypesEnvironment.forall(_.isWellConstructed))
    val ba = basicAssumptions
    val bc = basicConsEnvironment
    val bt = basicTypesEnvironment
    val se = safe_equal(Application(Abstraction(x, t), x), t)
    assert(se.isWellConstructed && se.typ == Bool)
    val ret = Theorem(se, ba, bc, bt)
    assert(ret.f.isWellConstructed && ret.f.typ == Bool && ret.c.forall(_.isWellConstructed) && ret.cEnv.forall(_.isWellConstructed) && ret.tEnv.forall(_.isWellConstructed) )
    check(ret.isWellConstructed)
    ret
  }.ensuring(_.isWellConstructed)

  //Eta-conversion of lambda calculus, i.e Abstraction of Application does nothing
  //
  //  |- (\x. t(x))=t )
  def ETA(x : Variable, t: Term): Theorem = {
    require(t.typ.in == x.typ && !t.freeVariables.contains(x) && x.isWellConstructed && t.isWellConstructed)
    val abap = Abstraction(x, Application(t, x))
    assert(basicAssumptions.forall(_.isWellConstructed))
    assert(basicConsEnvironment.forall(_.isWellConstructed))
    assert(basicTypesEnvironment.forall(_.isWellConstructed))
    val ba = basicAssumptions
    val bc = basicConsEnvironment
    val bt = basicTypesEnvironment
    assert(abap.typ == Func(x.typ, Application(t, x).typ))
    assert(Application(t, x).typ == t.typ.out)
    val se = safe_equal(abap, t)
    assert(abap.isWellConstructed)
    assert(se.isWellConstructed && safe_equal(abap, t).typ == Bool)
    val ret = Theorem(se, ba, bc, bt) // precond safe_equal, adt for theorem
    assert(ret.f.isWellConstructed && ret.f.typ == Bool && ret.c.forall(_.isWellConstructed) && ret.cEnv.forall(_.isWellConstructed) && ret.tEnv.forall(_.isWellConstructed) )
    check(ret.isWellConstructed)
    ret
  }.ensuring(_.isWellConstructed)

  //Assume something to be true
  //
  // {p} |-p
  def ASSUME(tt: Term): Theorem ={
    require(tt.typ == Bool && tt.isWellConstructed)
    //assert(basicAssumptions.forall(_.isWellConstructed))
    //assert(basicEnvironment.forall(_.isWellConstructed))
    //forallUnion[Term](basicAssumptions, List(tt), _.isWellConstructed)
    //assert((basicAssumptions++List(tt)).forall(_.isWellConstructed))
    assert(basicAssumptions.forall(_.isWellConstructed))
    assert(basicConsEnvironment.forall(_.isWellConstructed))
    assert(basicTypesEnvironment.forall(_.isWellConstructed))
    val bc = basicConsEnvironment
    val ba = basicAssumptions++List(tt)
    val bt = basicTypesEnvironment
    val res = Theorem(tt, ba, bc, bt)
    val pr = res.f.isWellConstructed && res.f.typ == Bool && res.c.forall(_.isWellConstructed) && res.cEnv.forall(_.isWellConstructed)
    assert(pr)
    //assert(pr)
    //wcimpwc(res)
    assert((res.f.isWellConstructed && res.f.typ == Bool && res.c.forall(_.isWellConstructed) && res.cEnv.forall(_.isWellConstructed)) == res.isWellConstructed)
    check(res.isWellConstructed)
    res
  }.ensuring(_.isWellConstructed)

  // Connects equaliy with deduction
  // |-p=q    |-p
  //      |-q
  def _EQ_MP(eq:Theorem, p: Theorem): Theorem ={
    require(
      (eq.f match {
        case Application(Application(Constant("=", Func(a, Func(b, Bool)), param_types), l), r) => l==p.f
        case _ => false
      }) && areCompatibleCons(eq.cEnv, p.cEnv) && areCompatibleTypes(eq.tEnv, p.tEnv) && eq.isWellConstructed && p.isWellConstructed
    )
    eq.f match {
      case Application(Application(Constant("=", Func(a, Func(b, Bool)), param_types), l), r) =>
        equalUnConstruct(eq)
        assert(l.typ == r.typ)
        forallUnion[Term](eq.c, p.c, _.isWellConstructed)
        forallUnion[ConstantDefinition](eq.cEnv, p.cEnv, _.isWellConstructed)
        forallUnion[TypeDefinition](eq.tEnv, p.tEnv, _.isWellConstructed)
        assert(r.isWellConstructed)
        assert(r.typ == l.typ)
        assert(l.typ == p.f.typ)
        assert(p.f.typ == Bool)
        assert(r.typ == Bool)
        val res = Theorem(r, (eq.c ++ p.c), (eq.cEnv ++ p.cEnv), (eq.tEnv++p.tEnv))
        check(res.isWellConstructed)
        res
    }
  }.ensuring(_.isWellConstructed)

   //Equivalence is equality of Boolean
   // q |-p   p |-q
   //   |- p=q
   def DEDUCT_ANTISYM_RULE(p: Theorem, q: Theorem): Theorem ={
     require(areCompatibleCons(p.cEnv, q.cEnv) && areCompatibleTypes(p.tEnv, q.tEnv) && p.isWellConstructed && q.isWellConstructed)
     val pcqf = p.c--List(q.f)
     val qcpf = q.c--List(p.f)
     forallRemove[Term](p.c, List(q.f), _.isWellConstructed)
     forallRemove[Term](q.c, List(p.f), _.isWellConstructed)
     assert(pcqf.forall(_.isWellConstructed))
     assert(qcpf.forall(_.isWellConstructed))
     forallUnion[Term](pcqf, qcpf, _.isWellConstructed)
     forallUnion[ConstantDefinition](p.cEnv, q.cEnv, _.isWellConstructed)
     forallUnion[TypeDefinition](p.tEnv, q.tEnv, _.isWellConstructed)
     val res = Theorem(safe_equal(p.f, q.f), (pcqf ++ qcpf), (p.cEnv++q.cEnv), (p.tEnv++q.tEnv))
     check(res.isWellConstructed)
     res
   }.ensuring(_.isWellConstructed)

  //Stainless accepts until here

   def _INST(thm: Theorem, x1: Variable, t1: Term): Theorem ={ // Instantiate but only if no free variable of t1 appears as a binding variable, i.e. no risk of capturing a variable.
     require(x1.typ == t1.typ && thm.isWellConstructed && x1.isWellConstructed && t1.isWellConstructed &&{
       thm.f.substitutionPossible(x1, t1)  && thm.c.forall(fo => fo.substitutionPossible(x1, t1))
     })
     val fs = thm.f.substitute(x1, t1)
     assert(fs.isWellConstructed)
     assert(thm.c.forall(_.isWellConstructed))
     assert(thm.c.forall(_.substitutionPossible(x1, t1)))
     assert(x1.isWellConstructed && t1.isWellConstructed && x1.typ == t1.typ)
     //require(li.forall(_.substitutionPossible(x1, t1)) && x1.isWellConstructed && t1.isWellConstructed && x1.typ == t1.typ)
     val cs = mapSubst(thm.c, x1, t1)
     assert(cs.forall(_.isWellConstructed))
     Theorem(fs, cs, thm.cEnv, thm.tEnv)
   }.ensuring(_.isWellConstructed)

   // Substitute type variable by type
   def INST_TYPE(thm: Theorem, alpha1: TypeVariable, tau1: HOL_type): Theorem ={
     require(tau1 != Unit && thm.isWellConstructed && alpha1.isWellConstructed && tau1.isWellConstructed)
     assert(thm.f.isWellConstructed)
     assert(thm.c.forall(_.isWellConstructed))
     val r = Theorem(thm.f.substituteType(alpha1, tau1), mapSubstType(thm.c, alpha1,tau1), thm.cEnv, thm.tEnv)
     check(r.isWellConstructed)
     r
   }.ensuring(_.isWellConstructed)


   // Definitions

   //Assert that a constant is only an alias
   def DEFINE_CONSTANT(c: Constant, t: Term): Theorem ={
     require(!t.hasFreeVariables && c.typ == t.typ && c.isWellConstructed && t.isWellConstructed)
     assert(ConstantDefinition(c,t).isWellConstructed)
     assert(basicAssumptions.forall(_.isWellConstructed))
     assert(List(ConstantDefinition(c,t)).forall(_.isWellConstructed))
     assert(basicConsEnvironment.forall(t => t.isWellConstructed))
     assert(basicConsEnvironment.forall(_.isWellConstructed))
     forallUnionCdef(basicConsEnvironment, List(ConstantDefinition(c,t)))
     assert((basicConsEnvironment++List(ConstantDefinition(c, t))).forall(_.isWellConstructed))
     assert(basicTypesEnvironment.forall(_.isWellConstructed))
     val res = Theorem(safe_equal(c, t), basicAssumptions, basicConsEnvironment:+ConstantDefinition(c, t), basicTypesEnvironment)
     check(res.isWellConstructed)
     res
   }.ensuring(_.isWellConstructed)

  def DEFINE_TYPE(nt: CustomType, bt: HOL_type, thm:Theorem, inF: Constant, outF: Constant): (Theorem, Theorem) ={
    require(
      nt.isWellConstructed && bt.isWellConstructed && thm.isWellConstructed && inF.isWellConstructed && outF.isWellConstructed &&
      inF.typ == Func(bt, nt) && outF.typ == Func(nt, bt) &&
      thm.c.forall(t => !t.hasFreeVariables) &&
      (thm.f match {case Application(p, t) => areCompatibleTypes(thm.tEnv, List(TypeDefinition(nt, bt, p))) && !p.hasFreeVariables && t.typ==bt case _ => false }) &&
      areCompatibleCons( thm.cEnv, List(ConstantDefinition(inF, inF) , ConstantDefinition(outF, outF)) )
    )
    val inFcd = ConstantDefinition(inF, inF)
    val outFcd =  ConstantDefinition(outF, outF)
    val a = Variable("a", nt)
    val r = Variable("r", bt)
    val P = thm.f match{ case Application(p, t) => p}
    val ntd = TypeDefinition(nt, bt, P) // |- A => in(out(a:A)) = a:A     A |- P(r:B) <=> (out(in(r)) = r)
    val ei = Application(outF, a)
    assert(ei.isWellConstructed)
    assert(ei.typ == outF.typ.out)
    assert(outF.typ.out == bt)
    assert(ei.typ == bt)
    val fi = Application(inF, ei)
    assert(fi.isWellConstructed)
    assert(fi.typ == a.typ)
    val th1 = Theorem(safe_equal(fi, a), thm.c, (thm.cEnv ++ List(inFcd,outFcd)), thm.tEnv++List(ntd))
    val gi =Application(outF, Application(inF, r))
    assert(Application(inF, r).isWellConstructed)
    assert(gi.isWellConstructed)
    assert(gi.typ == r.typ)
    val hi = Application(P, r)
    assert(thm.f.typ == P.typ.out )
    assert(P.isWellConstructed)
    assert(hi.isWellConstructed && hi.typ == Bool)
    val th2 = Theorem(safe_equal(Application(P, r), safe_equal(gi, r) ), thm.c, (thm.cEnv ++ List(inFcd,outFcd)), thm.tEnv++List(ntd))
    assert(safe_equal(fi, a).isWellConstructed && safe_equal(fi, a).typ == Bool)
    assert(thm.c.forall(_.isWellConstructed))
    assert(List(inFcd).forall(_.isWellConstructed))
    assert(outFcd.isWellConstructed)
    assert(List(outFcd).forall(_.isWellConstructed))
    forallUnion[ConstantDefinition](List(inFcd), List(outFcd), _.isWellConstructed)
    assert(List(inFcd, outFcd).forall(_.isWellConstructed))
    forallUnion[ConstantDefinition](thm.cEnv, List(inFcd, outFcd), _.isWellConstructed)
    forallUnion[TypeDefinition](thm.tEnv, List(ntd), _.isWellConstructed)
    check(th1.isWellConstructed)
    check(th2.isWellConstructed)
    (th1, th2)
  }.ensuring(res => res._1.isWellConstructed && res._2.isWellConstructed)
}
