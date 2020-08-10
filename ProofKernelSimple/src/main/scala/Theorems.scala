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
      case Application(Application(Constant("=", Func(a, Func(b, Bool))), l), r) =>
        assert(thm.isWellConstructed ==> Constant("=", Func(a, Func(b, Bool))).isWellConstructed)
        assert(thm.isWellConstructed ==> (a == b))
        assert(thm.isWellConstructed ==> (Application(Constant("=", Func(a, Func(b, Bool))), l).isWellConstructed && l.typ == a))
        assert(thm.isWellConstructed ==> (Application(Application(Constant("=", Func(a, Func(b, Bool))), l), r).isWellConstructed))
        assert(thm.isWellConstructed ==> (r.typ == Application(Constant("=", Func(a, Func(b, Bool))), l).typ.in))
        assert(thm.isWellConstructed ==> (r.typ == Func(a, Func(b, Bool)).out.in))
        assert(thm.isWellConstructed ==> (r.typ == b))
        check(thm.isWellConstructed ==> (a == b && l.typ == b && r.typ == a && l.typ == r.typ && l.isWellConstructed && r.isWellConstructed))
      case _ => false
    }
  }.ensuring(thm.isWellConstructed ==> (thm.f match {
    case Application(Application(Constant("=", Func(a, Func(b, Bool))), l), r) => a==b && l.typ == b && r.typ == a && l.typ == r.typ && l.isWellConstructed && r.isWellConstructed
    case _ => true
  }))

  def wcimpwc(res:Theorem): Unit ={
  }.ensuring((res.f.isWellConstructed && res.f.typ == Bool && res.c.forall(_.isWellConstructed) && res.env.forall(_.isWellConstructed)) == res.isWellConstructed)
  /////////////////////////////
  //End of Lemmas
  /////////////////////////////


  //Defines the conservative extension in which a theorem is expressed. Contains all definitions of constants.
  type Environment = List[ConstantDefinition]
  val basicEnvironment: Environment = List(ConstantDefinition(equal, equal))
  def findConflicts(env1: Environment, env2: Environment) : List[ConstantDefinition] = {
    val uni = env1  ++ env2
    uni.filter(cd1 => uni.exists(cd2 => cd1 conflicts cd2))
  }
  def areCompatible(env1: Environment, env2: Environment): Boolean = {
    val uni = env1 ++ env2
    val p = (cd1:ConstantDefinition) => uni.exists(cd2 => cd1 conflicts cd2)
    filterEmpty[ConstantDefinition](uni, p)
    !uni.exists(cd1 => uni.exists(cd2 => cd1 conflicts cd2) )
  }.ensuring(r => r == findConflicts(env1, env2).isEmpty) //help stainless

  //Define the context of a theorem, i.e. the right hand side of the sequent
  type Context = List[Term]
  val basicContext: Context = List()

  //Define Theorems, with a private constructor so that a theorem can only be created using the following inference rules.
  case class Theorem private (f: Term, c: Context, env: Environment) {
    def isWellConstructed: Boolean = f.isWellConstructed && f.typ == Bool && c.forall(_.isWellConstructed) && env.forall(_.isWellConstructed)
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
    Theorem(safe_equal(t,t), basicContext, basicEnvironment)
  }.ensuring(_.isWellConstructed)

  //Equality is transitive
  // |-s=t  |-t=u
  //    |-s=u
  def _TRANS(first: Theorem, second: Theorem): Theorem = {
    require(
      ((first.f, second.f) match {
        case (Application(Application(Constant("=", Func(a, Func(b, Bool))), s), t), Application(Application(Constant("=", Func(c, Func(d, Bool))), u), v)) => t == u
        case _ => false
      }) &&
        areCompatible(first.env, second.env)  && first.isWellConstructed && second.isWellConstructed
    )
    (first.f, second.f) match { //safe_equal precondition
      case (Application(Application(Constant("=", Func(a, Func(b, Bool))), s), t), Application(Application(Constant("=", Func(c, Func(d, Bool))), u), v)) =>
        assert(first.f.isWellConstructed && second.f.isWellConstructed)
        equalUnConstruct(first)
        equalUnConstruct(second)
        assert(s.typ == t.typ)
        assert(t.typ == u.typ)
        assert(u.typ == v.typ)
        forallUnion[Term](first.c, second.c, te => te.isWellConstructed)
        check((first.c ++ second.c).forall(_.isWellConstructed))
        forallUnion[ConstantDefinition](first.env, second.env, defi => defi.isWellConstructed)
        check((first.env ++ second.env).forall(_.isWellConstructed))
        Theorem(safe_equal(s,v), first.c ++ second.c, first.env ++ second.env)
    }
  }.ensuring(_.isWellConstructed)

  //Congruence property of equality
  //  |-s=t  |u=v
  //  |-s(u)=t(v)
  //  Types need to match
  def MK_COMB(first: Theorem, second:Theorem): Theorem = {
    require( first.isWellConstructed && second.isWellConstructed &&
      ((first.f, second.f) match {
        case (Application(Application(Constant("=", Func(a, Func(b, Bool))), s), t), Application(Application(Constant("=", Func(c, Func(d, Bool))), u), v)) => s.typ.in == u.typ && t.typ.in == v.typ
        case _ => false
      }) && areCompatible(first.env, second.env))
    (first.f, second.f) match {
      case (Application(Application(Constant("=", Func(a, Func(b, Bool))), s), t), Application(Application(Constant("=", Func(c, Func(d, Bool))), u), v)) =>
        assert(first.f.isWellConstructed && second.f.isWellConstructed)
        equalUnConstruct(first)
        equalUnConstruct(second)
        assert(s.typ == t.typ)
        assert(u.typ == v.typ)
        forallUnion[ConstantDefinition](first.env, second.env, defi => defi.isWellConstructed)
        forallUnion[Term](first.c, second.c, te => te.isWellConstructed)
        assert(Application(s, u).isWellConstructed && Application(t, v).isWellConstructed)
        Theorem(safe_equal(Application(s, u), Application(t, v)), first.c ++ second.c, first.env ++ second.env) // precond for safe_equal, adt for theorem, adt for application t, v
    }
  }.ensuring(_.isWellConstructed)


  //Abstraction rule
  //      |-s=t
  //  |-\x. s = \x.t
  def ABS(eq: Theorem, x: Variable): Theorem = { // Stainless needs help
    require((eq.f match {
      case Application(Application(Constant("=", Func(a, Func(b, Bool))), l), r) => true
      case _ => false
    }) && !eq.c.exists(t => t.freeVariables.contains(x))  && eq.isWellConstructed && x.isWellConstructed )
    eq.f match {
      case Application(Application(Constant("=", Func(a, Func(b, Bool))), l), r) =>
        equalUnConstruct(eq)
        assert(Abstraction(x, l).typ == Abstraction(x, r).typ)
        Theorem(safe_equal(Abstraction(x, l), Abstraction(x, r)), eq.c, eq.env)
    }
  }.ensuring(_.isWellConstructed)

  //Beta-conversion of lambda calculus, i.e Application of Abstraction does nothing
  //
  //  |- (\x. t)(x)=t
  def BETA(x : Variable, t: Term): Theorem = {
    require(x.isWellConstructed && t.isWellConstructed)
    assert(Application(Abstraction(x, t), x).typ == t.typ)
    assert(Application(Abstraction(x, t), x).isWellConstructed)
    assert(basicContext.forall(_.isWellConstructed))
    assert(basicEnvironment.forall(_.isWellConstructed))
    val se = safe_equal(Application(Abstraction(x, t), x), t)
    assert(se.isWellConstructed && se.typ == Bool)
    val ret = Theorem(se, basicContext, basicEnvironment)
    check(ret.isWellConstructed)
    ret
  }.ensuring(_.isWellConstructed)

  //Eta-conversion of lambda calculus, i.e Abstraction of Application does nothing
  //
  //  |- (\x. t(x))=t )
  def ETA(x : Variable, t: Term): Theorem = {
    require(t.typ.in == x.typ && !t.freeVariables.contains(x) && x.isWellConstructed && t.isWellConstructed)
    val abap = Abstraction(x, Application(t, x))
    assert(basicContext.forall(_.isWellConstructed))
    assert(basicEnvironment.forall(_.isWellConstructed))
    assert(abap.typ == Func(x.typ, Application(t, x).typ))
    assert(Application(t, x).typ == t.typ.out)
    val se = safe_equal(abap, t)
    assert(abap.isWellConstructed)
    assert(se.isWellConstructed && safe_equal(abap, t).typ == Bool)
    val res = Theorem(se, basicContext, basicEnvironment) // precond safe_equal, adt for theorem
    check(res.isWellConstructed)
    res
  }.ensuring(_.isWellConstructed)

  //Assume something to be true
  //
  // {p} |-p
  def ASSUME(f: Term): Theorem ={
    require(f.typ == Bool && f.isWellConstructed)
    //assert(basicContext.forall(_.isWellConstructed))
    //assert(basicEnvironment.forall(_.isWellConstructed))
    forallUnion[Term](basicContext, List(f), _.isWellConstructed)
    assert((basicContext++List(f)).forall(_.isWellConstructed))
    val res = Theorem(f, basicContext++List(f), basicEnvironment)
    assert(res.f.isWellConstructed && res.f.typ == Bool && res.c.forall(_.isWellConstructed) && res.env.forall(_.isWellConstructed))
    wcimpwc(res)
    assert((res.f.isWellConstructed && res.f.typ == Bool && res.c.forall(_.isWellConstructed) && res.env.forall(_.isWellConstructed)) == res.isWellConstructed)
    assert(res.isWellConstructed)
    res
  }.ensuring(_.isWellConstructed)

  // Connects equaliy with deduction
  // |-p=q    |-p
  //      |-q
  def _EQ_MP(eq:Theorem, p: Theorem): Theorem ={
    require(
      (eq.f match {
        case Application(Application(Constant("=", Func(a, Func(b, Bool))), l), r) => l==p.f
        case _ => false
      }) && areCompatible(eq.env, p.env) && eq.isWellConstructed && p.isWellConstructed
    )
    eq.f match {
      case Application(Application(Constant("=", Func(a, Func(b, Bool))), l), r) =>
        equalUnConstruct(eq)
        assert(l.typ == r.typ)
        forallUnion[Term](eq.c, p.c, _.isWellConstructed)
        forallUnion[ConstantDefinition](eq.env, p.env, _.isWellConstructed)
        assert(r.isWellConstructed)
        assert(r.typ == l.typ)
        assert(l.typ == p.f.typ)
        assert(p.f.typ == Bool)
        assert(r.typ == Bool)
        val res = Theorem(r, eq.c ++ p.c, eq.env ++ p.env)
        check(res.isWellConstructed)
        res
    }
  }.ensuring(_.isWellConstructed)
  /*
     //Equivalence is equality of Boolean
     // q |-p   p |-q
     //   |- p=q
     def DEDUCT_ANTISYM_RULE(p: Theorem, q: Theorem): Theorem ={
       require(areCompatible(p.env, q.env) && p.isWellConstructed && q.isWellConstructed)
       Theorem(safe_equal(p.f, q.f), (p.c - q.f) ++ (q.c - p.f), (p.env++q.env).unique)
     }.ensuring(_.isWellConstructed)

     def _INST(thm: Theorem, x1: Variable, t1: Term): Theorem ={ // Instantiate but only if no free variable of t1 appears as a binding variable, i.e. no risk of capturing a variable.
       require(x1.typ == t1.typ &&{
         val t1fv = t1.freeVariables
         thm.f.bindingVariables.forall(!t1fv.contains(_)) &&
           thm.c.forall(fo => fo.bindingVariables.forall(!t1fv.contains(_)))
       } && thm.isWellConstructed && x1.isWellConstructed && t1.isWellConstructed)
       Theorem(thm.f.substitute(x1, t1), thm.c.map(_.substitute(x1, t1)), thm.env)
     }.ensuring(_.isWellConstructed)

     // Substitute type variable by type
     def INST_TYPE(thm: Theorem, alpha1: TypeVariable, tau1: HOL_type): Theorem ={
       require(tau1 != Unit && thm.isWellConstructed && alpha1.isWellConstructed && tau1.isWellConstructed)
       Theorem(thm.f.substituteType(alpha1, tau1), thm.c.map(_.substituteType(alpha1, tau1)), thm.env)
     }.ensuring(_.isWellConstructed)

     // Definitions

     //Assert that a constant is only an alias
     def DEFINE_CONSTANT(c: Constant, t: Term): Theorem ={
       require(!t.hasFreeVariables && c.typ == t.typ && c.isWellConstructed && t.isWellConstructed)
       Theorem(safe_equal(c, t), basicContext, basicEnvironment:+ConstantDefinition(c, t))
     }.ensuring(_.isWellConstructed)
  */

  //tests
  /*
  def typeOf_test(t:Term): HOL_type = {
    t match {
      case Variable(name, k) => k
      case Abstraction(x, t) => Func(typeOf_test(x), typeOf_test(t))
      case Application(f, t) => typeOf_test(f).out
    }
  }*/
}
