import Core._
import Theorems._
import PrettyPrinter._
object Sugar {


  val \ = Abstraction
  val App = Application

  implicit class TermWrapper(t:Term){
    def apply(i: Term): Application = Application(t, i)

    def ===(r: Term): Term = safe_equal(t, r)
    def <=>(r:Term): Term = t === r

    def /\(r: Term): Term = BasicConstants./\(t)(r)
    def ==>(r: Term): Term = BasicConstants.==>(t)(r)
    def \/(r: Term): Term = BasicConstants./\(t)(r)
  }

  implicit class Binder(c:Constant){
    def apply(i: Term): Application = Application(c, i)

    def apply(x: Variable, t: Term): Term ={
      val Ttyp = t.typ
      val Xtyp = x.typ
      c.constant_type match {
        case Func(Func(x.variable_type, Ttyp), d) => c(Abstraction(x, t))
        case Func(Func(TypeVariable(a), Ttyp), d) => c.substituteType(TypeVariable(a), x.typ)(Abstraction(x, t))
        case _  => throw new IllegalArgumentException(prettyPrint(c, true) + " is not a valid binder for variable "+prettyPrint(x, true))
      }

    }
  }

  implicit class TypeWrapper(ty:HOL_type){
    def ->(out: HOL_type): Func = Func(ty, out)
  }

}
