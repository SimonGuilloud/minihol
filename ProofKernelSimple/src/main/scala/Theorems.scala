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
  def equalUnConstruct(thm: Theorem):Unit = {
    thm.f match {
      case Application(Application(Constant("=", Func(a, Func(b, Bool)), param_types), l), r) =>
        val cEq = Constant("=", Func(a, Func(b, Bool)), param_types)
        assert(thm.isWellConstructed ==> cEq.isWellConstructed)
        assert(thm.isWellConstructed ==> (a == b))
        assert(thm.isWellConstructed ==> (Application(cEq, l).isWellConstructed && l.typ == a))
        assert(thm.isWellConstructed ==> (Application(Application(cEq, l), r).isWellConstructed))
        assert(thm.isWellConstructed ==> (r.typ == Application(cEq, l).typ.in))
        assert(thm.isWellConstructed ==> (r.typ == Func(a, Func(b, Bool)).out.in))
        assert(thm.isWellConstructed ==> (r.typ == b))
        check(thm.isWellConstructed ==> (a == b && l.typ == b && r.typ == a && l.typ == r.typ && l.isWellConstructed && r.isWellConstructed))
      case _ => false
    }
  }.ensuring(thm.isWellConstructed ==> (thm.f match {
    case Application(Application(Constant("=", Func(a, Func(b, Bool)), param_types), l), r) => a==b && l.typ == b && r.typ == a && l.typ == r.typ && l.isWellConstructed && r.isWellConstructed
    case _ => true
  }))

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
        check((first.c ++ second.c).forall(_.isWellConstructed))
        forallUnion[ConstantDefinition](first.cEnv, second.cEnv, defi => defi.isWellConstructed)
        check((first.cEnv ++ second.cEnv).forall(_.isWellConstructed))
        Theorem(safe_equal(s,v), (first.c ++ second.c).unique, (first.cEnv ++ second.cEnv).unique, (first.tEnv ++ second.tEnv).unique)
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
        forallUnion[Term](first.c, second.c, te => te.isWellConstructed)
        assert(Application(s, u).isWellConstructed && Application(t, v).isWellConstructed)
        Theorem(safe_equal(Application(s, u), Application(t, v)), (first.c ++ second.c).unique, (first.cEnv ++ second.cEnv).unique, (first.tEnv ++ second.tEnv).unique) // precond for safe_equal, adt for theorem, adt for application t, v
    }
  }.ensuring(_.isWellConstructed)


  //Abstraction rule
  //      |-s=t
  //  |-\x. s = \x.t
  def ABS(eq: Theorem, x: Variable): Theorem = { // Stainless needs help
    require((eq.f match {
      case Application(Application(Constant("=", Func(a, Func(b, Bool)), param_types), l), r) => true
      case _ => false
    }) && !eq.c.exists(t => t.freeVariables.contains(x))  && eq.isWellConstructed && x.isWellConstructed )
    eq.f match {
      case Application(Application(Constant("=", Func(a, Func(b, Bool)), param_types), l), r) =>
        equalUnConstruct(eq)
        assert(Abstraction(x, l).typ == Abstraction(x, r).typ)
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
    val se = safe_equal(Application(Abstraction(x, t), x), t)
    assert(se.isWellConstructed && se.typ == Bool)
    val ret = Theorem(se, basicAssumptions, basicConsEnvironment, basicTypesEnvironment)
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
    assert(abap.typ == Func(x.typ, Application(t, x).typ))
    assert(Application(t, x).typ == t.typ.out)
    val se = safe_equal(abap, t)
    assert(abap.isWellConstructed)
    assert(se.isWellConstructed && safe_equal(abap, t).typ == Bool)
    val res = Theorem(se, basicAssumptions, basicConsEnvironment, basicTypesEnvironment) // precond safe_equal, adt for theorem
    check(res.isWellConstructed)
    res
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
    val be = basicConsEnvironment
    val bc = basicAssumptions++List(tt)
    val res = Theorem(tt, bc, be, basicTypesEnvironment)
    val pr = res.f.isWellConstructed && res.f.typ == Bool && res.c.forall(_.isWellConstructed) && res.cEnv.forall(_.isWellConstructed)
    assert(res.f.isWellConstructed && res.f.typ == Bool && res.c.forall(_.isWellConstructed) && res.cEnv.forall(_.isWellConstructed))
    //assert(pr)
    //wcimpwc(res)
    assert((res.f.isWellConstructed && res.f.typ == Bool && res.c.forall(_.isWellConstructed) && res.cEnv.forall(_.isWellConstructed)) == res.isWellConstructed)
    assert(res.isWellConstructed)
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
        val res = Theorem(r, (eq.c ++ p.c).unique, (eq.cEnv ++ p.cEnv).unique, (eq.tEnv++p.tEnv).unique)
        check(res.isWellConstructed)
        res
    }
  }.ensuring(_.isWellConstructed)

   //Equivalence is equality of Boolean
   // q |-p   p |-q
   //   |- p=q
   def DEDUCT_ANTISYM_RULE(p: Theorem, q: Theorem): Theorem ={
     require(areCompatibleCons(p.cEnv, q.cEnv) && areCompatibleTypes(p.tEnv, q.tEnv) && p.isWellConstructed && q.isWellConstructed)
     Theorem(safe_equal(p.f, q.f), ((p.c - q.f) ++ (q.c - p.f)).unique, (p.cEnv++q.cEnv).unique, (p.tEnv++q.tEnv).unique)
   }.ensuring(_.isWellConstructed)

   def _INST(thm: Theorem, x1: Variable, t1: Term): Theorem ={ // Instantiate but only if no free variable of t1 appears as a binding variable, i.e. no risk of capturing a variable.
     require(x1.typ == t1.typ &&{
       val t1fv = t1.freeVariables
       thm.f.substitutionPossible(x1, t1) &&
         thm.c.forall(fo => fo.substitutionPossible(x1, t1))
     } && thm.isWellConstructed && x1.isWellConstructed && t1.isWellConstructed)
     Theorem(thm.f.substitute(x1, t1), thm.c.map(_.substitute(x1, t1)), thm.cEnv, thm.tEnv)
   }.ensuring(_.isWellConstructed)

   // Substitute type variable by type
   def INST_TYPE(thm: Theorem, alpha1: TypeVariable, tau1: HOL_type): Theorem ={
     require(tau1 != Unit && thm.isWellConstructed && alpha1.isWellConstructed && tau1.isWellConstructed)
     Theorem(thm.f.substituteType(alpha1, tau1), thm.c.map(_.substituteType(alpha1, tau1)), thm.cEnv, thm.tEnv)
   }.ensuring(_.isWellConstructed)

   // Definitions

   //Assert that a constant is only an alias
   def DEFINE_CONSTANT(c: Constant, t: Term): Theorem ={
     require(!t.hasFreeVariables && c.typ == t.typ && c.isWellConstructed && t.isWellConstructed)
     Theorem(safe_equal(c, t), basicAssumptions, basicConsEnvironment:+ConstantDefinition(c, t), basicTypesEnvironment)
   }.ensuring(_.isWellConstructed)

  def DEFINE_TYPE(nt: CustomType, bt: HOL_type, thm:Theorem, inF: Constant, outF: Constant): (Theorem, Theorem) ={
    require(
      nt.isWellConstructed && bt.isWellConstructed && thm.isWellConstructed && inF.isWellConstructed && outF.isWellConstructed )
    require(
      inF.typ == Func(bt, nt) && outF.typ == Func(nt, bt))
    require(
      thm.c.forall(t => !t.hasFreeVariables) &&
      (thm.f match {case Application(p, t) => areCompatibleTypes(thm.tEnv, List(TypeDefinition(nt, bt, p))) && !p.hasFreeVariables case _ => false}) &&
      areCompatibleCons( thm.cEnv, List(ConstantDefinition(inF, inF) , ConstantDefinition(outF, outF)) )
    )
    val inFcd = ConstantDefinition(inF, inF)
    val outFcd =  ConstantDefinition(outF, outF)
    val a = Variable("a", nt)
    val r = Variable("r", bt)
    val P = thm.f match{ case Application(p, t) => p}
    val ntd = TypeDefinition(nt, bt, P)
    val th1 = Theorem(safe_equal(Application(inF, Application(outF, a)), a), thm.c, (thm.cEnv ++ List(inFcd,outFcd)).unique, (thm.tEnv:+ntd).unique)
    val th2 = Theorem(safe_equal(Application(P, r), safe_equal(Application(outF, Application(inF, r)), r) ), thm.c, (thm.cEnv ++ List(inFcd,outFcd)).unique, (thm.tEnv:+ntd).unique)
    (th1, th2)
  }.ensuring(res => res._1.isWellConstructed && res._2.isWellConstructed)

}
