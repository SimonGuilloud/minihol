import stainless.lang.{print =>pprint, _}
import stainless.collection._
import stainless.annotation._
import stainless.math._
import stainless.proof._




object Core {
  //Useful lemmas
  def filterEmpty[T]( @induct maList: List[T], p: T=>Boolean) : Unit ={
  }.ensuring(_ => maList.filter(p).isEmpty == !maList.exists(p))

  def termOKimpliesTypeOK(te: Term): Unit ={te match {
        case Variable(name, variable_type) => check(te.isWellConstructed ==> variable_type.isWellConstructed)
        case Abstraction(x, t) => {
          assert(te.isWellConstructed ==> (x.variable_type.isWellConstructed))
          assert(te.isWellConstructed ==> t.isWellConstructed)
          termOKimpliesTypeOK(t)
          check(te.isWellConstructed ==> (x.variable_type.isWellConstructed && t.typ.isWellConstructed))
        }
        case Application(f, t) => {
          assert(te.isWellConstructed ==> (t.isWellConstructed && f.isWellConstructed))
          termOKimpliesTypeOK(f)
          termOKimpliesTypeOK(t)
          assert(te.isWellConstructed ==> (f.typ.isWellConstructed && t.typ.isWellConstructed))
          assert((f.typ.isWellConstructed && t.typ.isWellConstructed) ==> te.typ.isWellConstructed)
          check(te.isWellConstructed ==> te.typ.isWellConstructed)
        }
        case Constant(name, constant_type, param_types) => check(te.isWellConstructed ==> constant_type.isWellConstructed)
      }
  }.ensuring(te.isWellConstructed ==> te.typ.isWellConstructed)

  def equalIsOK: Unit = {
    assert(equal.constant_type.isWellConstructed)
    assert(equal.constant_type match {
      case Func(lt, Func(rt, Bool)) => lt == rt
      case _ => false
    })
    check(equal.isWellConstructed)
  }.ensuring(equal.isWellConstructed)



  abstract sealed class HOL_type() {
    def isWellConstructed: Boolean = this match {
      case Unit => true
      case Bool => true
      case Ind => true
      case Func(input_type, output_type) => input_type.isWellConstructed && output_type.isWellConstructed && output_type != Unit
      case TypeVariable(name) => true
      case CustomType(name) => true
    }
    def in: HOL_type = this match {
      case Unit => this
      case Bool => Unit
      case Ind => Unit
      case Func(in, out) => in
      case TypeVariable(name) => Unit
      case CustomType(name) => Unit
    }
    def out: HOL_type = {
      this match {
        case Unit => this
        case Bool => this
        case Ind => this
        case Func(in, out) => out
        case TypeVariable(name) => this
        case CustomType(name) => this
      }
    }.ensuring(this == Unit || _ != Unit)
    def type_substituteType(alpha1: HOL_type, tau1: HOL_type): HOL_type = {
      require(tau1 != Unit && this.isWellConstructed && alpha1.isWellConstructed && tau1.isWellConstructed)
      this match {
        case Unit => this
        case Bool => this
        case Ind => this
        case Func(input_type, output_type) =>
          Func(input_type.type_substituteType(alpha1, tau1), output_type.type_substituteType(alpha1, tau1))
        case TypeVariable(name) => if (this == alpha1) tau1 else this
        case CustomType(name) => this
      }
    }.ensuring(_.isWellConstructed)
    def freeTypeVariables: List[TypeVariable] = this match {
      case Unit => List.empty
      case Bool => List.empty
      case Ind => List.empty
      case Func(input_type, output_type) => (input_type.freeTypeVariables ++ output_type.freeTypeVariables).unique
      case TypeVariable(name) => List(TypeVariable(name))
      case CustomType(name) => List.empty
    }
  }
  case object Unit extends HOL_type
  case object Bool extends HOL_type
  case object Ind extends HOL_type
  case class Func(input_type: HOL_type, output_type: HOL_type) extends HOL_type
  case class TypeVariable(name: String) extends HOL_type
  case class CustomType(name:String) extends HOL_type

  @inlineInvariant
  sealed abstract class Term {
    def isWellConstructed: Boolean = this match {
      case Variable(name, variable_type) => variable_type.isWellConstructed && variable_type != Unit
      case Abstraction(x, t) => x.variable_type.isWellConstructed && t.isWellConstructed
      case Application(f, t) => f.isWellConstructed && t.isWellConstructed && f.typ.in == t.typ
      case Constant(name, constant_type, param_types) => constant_type.isWellConstructed && constant_type != Unit &&
        ((name == "=") ==> (constant_type match {
          case Func(lt, Func(rt, Bool)) => lt == rt
          case _ => false
        }))
     }
    def height: BigInt = {
      this match {
        case Variable(name, variable_type) => BigInt(1)
        case Abstraction(x, t) => t.height + BigInt(1)
        case Application(f, t) => f.height + t.height
        case Constant(name, constant_type, param_types) => BigInt(1)
      }
    } .ensuring(_ >= BigInt(1))
    def typ: HOL_type = {
      this match {
        case Variable(name, variable_type) => variable_type
        case Abstraction(x, t) => Func(x.variable_type, t.typ)
        case Application(f, t) => f.typ.out
        case Constant(name, constant_type, param_types) => constant_type
      }
    }.ensuring(r => r != Unit)
    def freeVariables: List[Variable] = this match {
      case Variable(name, variable_type) => List(Variable(name, variable_type))
      case Abstraction(x, t) => t.freeVariables - x
      case Application(f, t) => (f.freeVariables ++ t.freeVariables).unique
      case Constant(name, constant_type, param_types) => List.empty
    }
    def hasFreeVariables: Boolean = !this.freeVariables.isEmpty
    def occuringVariables: List[Variable] = this match {
      case Variable(name, variable_type) => List(Variable(name, variable_type))
      case Abstraction(x, t) => (t.occuringVariables:+ x).unique
      case Application(f, t) => (f.occuringVariables ++ t.occuringVariables).unique
      case Constant(name, constant_type, param_types) => List.empty
    }
    def bindingVariables: List[Variable] = this match {
      case Variable(name, variable_type) => List.empty
      case Abstraction(x, t) => List(x)
      case Application(f, t) => (f.bindingVariables ++ t.bindingVariables).unique
      case Constant(name, constant_type, param_types) => List.empty
    }
    def substitutionPossible(x1: Variable, t1: Term): Boolean = {
      decreases(this.height)
      this.isWellConstructed && {
        val t1fv = t1.freeVariables
        (x1.typ == t1.typ) && (!t1fv.contains(x1) || {
          this match {
            case Variable(name, variable_type) => true
            case Abstraction(y, t) =>
              if (y == x1) true
              else if (t1fv.contains(y) && !t.freeVariables.contains(x1)) true //actually useless line because the call on the next line will return this if the conditions are satisfied
              else if (!t1fv.contains(y)){
                assert(t.height<this.height)
                t.substitutionPossible(x1, t1)
              }
              else false
            case Application(f, t) => {
              assert(this.height == f.height + t.height)
              assert(f.height < this.height && t.height < this.height)
              f.substitutionPossible(x1, t1) && t.substitutionPossible(x1, t1)
            }
            case Constant(name, constant_type, param_types) => true
          }
        })
      }
    }

    def substitute(x1: Variable, t1: Term): Term = {
      require(this.isWellConstructed && t1.isWellConstructed && x1.isWellConstructed && x1.typ == t1.typ && this.substitutionPossible(x1, t1) ) //capture-avoiding substitution, but only partial. No renaming.
      decreases(this.height)
      val t1fv = t1.freeVariables
      if (!this.freeVariables.contains(x1)) this
      else this match {
        case Variable(name, variable_type) => if (this == x1) t1 else this
        case Abstraction(y, t) => {
          if (y == x1) this
          else if (t1fv.contains(y) && !t.freeVariables.contains(x1)) this //actually useless line because the call on the next line will return this if the conditions are satisfied
          else Abstraction(y, t.substitute(x1, t1))
          //else throw new Error("Substitute: The algorithm should not reach this state")
          // fails if t1fv.contains(y) and t.freeVariables.contains(x1), i.e. by replacing x1 by t this step would catch the free variable y in t.
        }
        case Application(f, t) =>
          assert(f.height < this.height)
          assert(t.height < this.height)
          assert(f.substitutionPossible(x1, t1))
          assert(t.substitutionPossible(x1, t1))
          Application(f.substitute(x1, t1), t.substitute(x1, t1))
        case Constant(name, constant_type, param_types) => this
      }
    }.ensuring( r => r.isWellConstructed && (t1.isInstanceOf[Variable] ==> (r.height == this.height)) && (r.typ == this.typ))
    def substituteType(alpha1: TypeVariable, tau1: HOL_type): Term = {
      require(this.isWellConstructed && alpha1.isWellConstructed && tau1.isWellConstructed && tau1 != Unit)
      decreases(this.height)
      termOKimpliesTypeOK(this)
      check(this.typ.isWellConstructed)
      this match {
        case Variable(name, variable_type) => {
          Variable(name, variable_type.type_substituteType(alpha1, tau1))
        }
        case Abstraction(x, t) => {
          termOKimpliesTypeOK(t)
          val r = Abstraction(Variable(x.name, x.variable_type.type_substituteType(alpha1, tau1)), t.substituteType(alpha1, tau1))
          check(r.isWellConstructed) //hard
          r
        }
        case Application(f, t) =>
          assert(f.height < this.height)
          assert(t.height < this.height)
          assert(f.typ.in == t.typ)
          assert(f.isWellConstructed)
          termOKimpliesTypeOK(f)
          assert(f.isWellConstructed ==> f.typ.isWellConstructed)
          termOKimpliesTypeOK(t)
          assert(f.typ.isWellConstructed)
          val ft = f.substituteType(alpha1, tau1)
          val tt = t.substituteType(alpha1, tau1)
          assert(ft.typ == f.typ.type_substituteType(alpha1, tau1))
          assert(ft.typ.in == f.typ.type_substituteType(alpha1, tau1).in)
          assert(f.typ.type_substituteType(alpha1, tau1).in == f.typ.in.type_substituteType(alpha1, tau1))
          assert(f.typ.in.type_substituteType(alpha1, tau1) == t.typ.type_substituteType(alpha1, tau1))
          assert(tt.typ == t.typ.type_substituteType(alpha1, tau1))
          assert(ft.typ.in == tt.typ)
          assert(Application(ft, tt).typ == f.substituteType(alpha1, tau1).typ.out)
          assert(f.substituteType(alpha1, tau1).typ.out == f.typ.type_substituteType(alpha1, tau1).out)
          assert(f.substituteType(alpha1, tau1).typ.out == f.typ.out.type_substituteType(alpha1, tau1))
          assert(f.typ.out == this.typ)
          check(Application(f.substituteType(alpha1, tau1), t.substituteType(alpha1, tau1)).typ == this.typ.type_substituteType(alpha1, tau1) )
          val r = Application(f.substituteType(alpha1, tau1), t.substituteType(alpha1, tau1))
          check(r.isWellConstructed) //hard
          r
        case Constant(name, constant_type, param_types) =>
          val p = name == "=" ==> (constant_type match {
            case Func(rt, Func(lt, Bool)) => (rt == lt) && (rt.type_substituteType(alpha1, tau1) == lt.type_substituteType(alpha1, tau1))
            case _ => false})
          assert(p)
          val ctt = constant_type.type_substituteType(alpha1, tau1)
          if (name == "="){
            assert(ctt.isInstanceOf[Func])
            assert(ctt.out.isInstanceOf[Func])
            assert(constant_type.out.out == Bool)
            assert(ctt.out == constant_type.out.type_substituteType(alpha1, tau1))
            assert(ctt.out.out == constant_type.out.out.type_substituteType(alpha1, tau1))
            assert(ctt match { case Func(ltt, Func(rtt, Bool)) => true case _ => false})
            ctt match {case Func(ltt, Func(rtt, Bool)) =>
              val tri = (name=="=") ==> (ltt == rtt)
              assert(tri)
              constant_type match {
                case Func(rt, Func(lt, Bool)) =>
                  assert(ltt == rtt)
                  assert(tri)
                  val r = Constant(name, ctt, param_types-alpha1)
                  check(r.isWellConstructed) //hard
                  r
              }
            }
          }
          else{
            val r = Constant(name, ctt, param_types-alpha1)
            check(r.isWellConstructed)
            r
          }
      }
    }.ensuring(r => r.isWellConstructed && r.height == this.height && r.typ == this.typ.type_substituteType(alpha1, tau1))
    def freeTypeVariables: List[TypeVariable] = this match {
      case Variable(name, variable_type) => variable_type.freeTypeVariables
      case Abstraction(x, t) => (x.freeTypeVariables ++ t.freeTypeVariables).unique
      case Application(f, t) => (f.freeTypeVariables ++ t.freeTypeVariables).unique
      case Constant(name, constant_type, param_types) => (constant_type.freeTypeVariables ++ param_types).unique
    }
 }
  case class Variable(name: String, variable_type: HOL_type) extends Term
  case class Abstraction(x: Variable, t: Term) extends Term
  case class Application(f: Term, t: Term) extends Term
  case class Constant(name: String, constant_type: HOL_type, param_types: List[TypeVariable]) extends Term




   //define primitive constant equality.
   //It has no definition, only properties which are defined by primitives rules
   //To make sure the user can't "define" equality, we force the definition  that "equal" == "equal"
   private val A = TypeVariable("A")
   val equal: Constant = Constant("=", Func(A, Func(A, Bool)), List(A))

   def safe_equal(l:Term, r:Term): Term = {
     require(l.isWellConstructed && r.isWellConstructed && l.typ == r.typ)
     termOKimpliesTypeOK(l)
     termOKimpliesTypeOK(r)
     assert(l.typ.isWellConstructed)
     equalIsOK
     val nq = equal.substituteType(A, l.typ)
     assert(nq.isWellConstructed)
     assert(l.typ != Unit)
     assert(r.typ != Unit)
     assert(equal.typ == Func(A, Func(A, Bool)))
     assert(Func(A, Bool).type_substituteType(A, l.typ) == Func(l.typ, Bool))
     assert(nq.typ == Func(l.typ, Func(l.typ, Bool)))
     assert(nq.typ.in == l.typ)
     val nqf = Application(nq, l)
     assert(nqf.isWellConstructed)
     assert(nqf.typ == Func(l.typ, Bool))
     assert(nqf.typ.in == r.typ)
     assert(nqf.typ.out == Bool)
     val res = Application(nqf, r)
     check(res.typ == Bool && res.isWellConstructed)
     res
   }.ensuring(res => res.typ == Bool && res.isWellConstructed)

}
