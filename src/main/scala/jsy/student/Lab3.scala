package jsy.student

import jsy.lab3.Lab3Like
import jsy.util.JsyApplication

object Lab3 extends JsyApplication with Lab3Like {
  import jsy.lab3.ast._
  
  /*
   * CSCI 3155: Lab 3 
   * Brandon Zink
   * 
   * Partner: Cameron Connor
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace the '???' expression with your code in each function.
   *
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   * 
   * Your lab will not be graded if it does not compile.
   * 
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert. Simply put in a
   * '???' as needed to get something  that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */
  
  /*
   * The implementations of these helper functions for conversions can come
   * Lab 2. The definitions for the new value type for Function are given.
   */
  
  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n
      case B(b) => if(b) 1.0 else 0.0
      case S(s) => s match {
        case "" => 0.0
        case _ => try {
          s.toDouble
        } catch {
          case _ : NumberFormatException => Double.NaN
        }
      }
      case _ => Double.NaN
    }
  }
  
  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case B(b) => b
      case N(n) => if(n == 0 || n == Double.NaN) false else true
      case S(s) => if(s.equals("")) false else true
      case Function(_, _, _) => true
      case Undefined => false
    }
  }
  
  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case S(s) => s
      case B(b) => b.toString
      case N(n) => prettyNumber(n)
        // Here in toStr(Function(_, _, _)), we will deviate from Node.js that returns the concrete syntax
        // of the function (from the input program).
      case Function(_, _, _) => "function"
      case Undefined => "undefined"
    }
  }

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1))
    require(isValue(v2))
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      case (S(s1), S(s2)) => bop match {
        case Lt => if (s1.compareTo(s2) == -1) true else false
        case Le => if (s1.compareTo(s2) == 1) false else true
        case Gt => if (s1.compareTo(s2) == 1) true else false
        case Ge => if (s1.compareTo(s2) == -1) false else true
      }
      case _ => bop match {
        case Lt => toNumber(v1) < toNumber(v2)
        case Le => toNumber(v1) <= toNumber(v2)
        case Gt => toNumber(v1) > toNumber(v2)
        case Ge => toNumber(v1) >= toNumber(v2)
      }
    }
  }


  /* Big-Step Interpreter with Dynamic Scoping */
  
  /*
   * Start by copying your code from Lab 2 here.
   */
  def eval(env: Env, e: Expr): Expr = {
    e match {
      /* Base Cases */
      case v if isValue(v) => v
      case Var(s) => lookup(env, s)
      /* Inductive Cases */
        // Unary operators
      case Unary(Neg, e1) => N(-toNumber(eval(env, e1)))
      case Unary(Not, e1) => B(!toBoolean(eval(env, e1)))
        // Arithmetic operators
      case Binary(Minus, e1, e2) => N(toNumber(eval(env, e1)) - toNumber(eval(env, e2)))
      case Binary(Times, e1, e2) => N(toNumber(eval(env, e1)) * toNumber(eval(env, e2)))
      case Binary(Div, e1, e2) => N(toNumber(eval(env, e1)) / toNumber(eval(env, e2)))
        // Extra cases to handle string concatenation
      case Binary(Plus, e1, e2) => (eval(env, e1), eval(env, e2)) match {
        case (S(str), _) => S(str + toStr(e2))
        case (_, S(str)) => S(toStr(e1) + str)
        case (_, _) => N(toNumber(eval(env, e1)) + toNumber(eval(env, e2)))
      }
        // Equalities
      case Binary(Eq, e1, e2) => (eval(env, e1), eval(env, e2)) match {
        case (Function(_, _, _), _) => throw DynamicTypeError(e)
        case (_, Function(_, _, _)) => throw DynamicTypeError(e)
        case _ => if(eval(env, e1) == eval(env, e2)) B(true) else B(false)
      }
      case Binary(Ne, e1, e2) => (eval(env, e1), eval(env, e2)) match {
        case (Function(_, _, _), _) => throw DynamicTypeError(e)
        case (_, Function(_, _, _)) => throw DynamicTypeError(e)
        case _ => if(eval(env, e1) == eval(env, e2)) B(false) else B(true)
      }
        // Boolean Operators
      case Binary(And, e1, e2) => if(toBoolean(eval(env, e1))) eval(env, e2) else B(false)
      case Binary(Or, e1, e2) => if(toBoolean(eval(env, e1))) B(true) else eval(env, e2)
      case Binary(Seq, e1, e2) => eval(env, e1); eval(env, e2)
        // Inequalities
      case Binary(Lt, e1, e2) => B(inequalityVal(Lt, e1, e2))
      case Binary(Le, e1, e2) => B(inequalityVal(Le, e1, e2))
      case Binary(Gt, e1, e2) => B(inequalityVal(Gt, e1, e2))
      case Binary(Ge, e1, e2) => B(inequalityVal(Ge, e1, e2))
        // Functions
      case Call(e1, e2) => (eval(env, e1), eval(env, e2)) match {
        case (Function(None, x, b), _) => eval(extend(env, x, eval(env, e2)), b)
        case (Function(Some(x1), x2, b), _) =>
          eval(extend(extend(env, x1, eval(env, e1)), x2, eval(env, e2)), b)
        case _ => throw DynamicTypeError(e)
      }
        // Print, Constant Declaration
      case Print(e1) => println(pretty(eval(env, e1))); Undefined
      case ConstDecl(x, e1, e2) => eval(extend(env, x, eval(env, e1)), e2)
        // Conditional
      case If(e1, e2, e3) => if(toBoolean(eval(env, e1))) eval(env, e2) else eval(env, e3)

      case _ => Undefined
    }
  }
    

  /* Small-Step Interpreter with Static Scoping */

  def iterate(e0: Expr)(next: (Expr, Int) => Option[Expr]): Expr = {
    def loop(e: Expr, n: Int): Expr = next(e, n) match {
      case Some(ep) => loop(ep, n + 1)
      case None => e
    }
    loop(e0, 0)
  }
  
  def substitute(e: Expr, v: Expr, x: String): Expr = {
    require(isValue(v))
    e match {
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1) => Print(substitute(e1, v, x))
      case Unary(uop, e1) => Unary(uop, substitute(e1, v, x))
      case Binary(bop, e1, e2) => Binary(bop, substitute(e1, v, x), substitute(e2, v, x))
      case If(e1, e2, e3) => If(substitute(e1, v, x), substitute(e2, v, x), substitute(e3, v, x))
      case Call(e1, e2) => Call(substitute(e1, v, x), substitute(e2, v, x))
      case Var(y) => if (y == x) v else Var(y)
      case Function(None, y, e1) =>
        if (y == x) Function(None, y, e1)
        else Function(None, y, substitute(e1, v, x))
      case Function(Some(y1), y2, e1) =>
        if (y1 == x || y2 == x) Function(Some(y1), y2, e1)
        else Function(Some(y1), y2, substitute(e1, v, x))
      case ConstDecl(y, e1, e2) =>
        if (y == x) ConstDecl(y, substitute(e1, v, x), e2)
        else ConstDecl(y, substitute(e1, v, x), substitute(e2, v, x))
    }
  }
    
  def step(e: Expr): Expr = {
    e match {
      /* Base Cases: Do Rules */
        // Do Unary
      case Unary(Neg, v1) if isValue(v1) => N(-toNumber(v1))
      case Unary(Not, v1) if isValue(v1) => B(!toBoolean(v1))
        // Catch short-circuit binary operators first
      case Binary(And, v1, e2) if isValue(v1) => if (toBoolean(v1)) e2 else v1
      case Binary(Or, v1, e2) if isValue(v1) => if (toBoolean(v1)) v1 else e2
      case Binary(Seq, v1, e2) if isValue(v1) => e2 // FIXME
        // Do Binary for arithmetic and inequality operators
      case Binary(bop, v1, v2) if isValue(v1) && isValue(v2) => bop match {
        case Plus => (v1, v2) match {
          case (S(str), _) => S(str + toStr(v2))
          case (_, S(str)) => S(toStr(v1) + str)
          case _ => N(toNumber(v1) + toNumber(v2))
        }
        case Minus => N(toNumber(v1) - toNumber(v2))
        case Times => N(toNumber(v1) * toNumber(v2))
        case Div => N(toNumber(v1) / toNumber(v2))
        case Eq => (v1, v2) match {
          case (Function(_, _, _), _) => throw DynamicTypeError(e)
          case (_, Function(_, _, _)) => throw DynamicTypeError(e)
          case _ => B(v1 == v2)
        }
        case Ne =>  (v1, v2) match {
          case (Function(_, _, _), _) => throw DynamicTypeError(e)
          case (_, Function(_, _, _)) => throw DynamicTypeError(e)
          case _ => B(v1 != v2)
        }
        case Lt => B(inequalityVal(Lt, v1, v2))
        case Le => B(inequalityVal(Le, v1, v2))
        case Gt => B(inequalityVal(Gt, v1, v2))
        case Ge => B(inequalityVal(Ge, v1, v2))

      }

      case ConstDecl(x, v1, e2) if isValue(v1) => substitute(e2, v1, x)
      case If(v1, e2, e3) if isValue(v1) => if (toBoolean(v1)) e2 else e3
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined

      case Call(v1, v2) if isValue(v1) && isValue(v2) => (v1, v2) match {
        case (Function(None, x, e1), _) => substitute(e1, v2, x)
        case (Function(Some(x1), x2, e1), _) => substitute(substitute(e1, v1, x1), v2, x2)
        case _ => throw DynamicTypeError(e)
      }

      /* Inductive Cases: Search Rules */
      case Unary(uop, e1) => Unary(uop, step(e1))

      case Binary(bop, e1, e2) => (bop, e1, e2) match {
        case (Eq | Ne, Function(_, _, _), _) if isValue(e1) => throw DynamicTypeError(e)
        case (Eq | Ne, _, _) if isValue(e1) => Binary(bop, e1, step(e2))
        case (Plus | Minus | Times | Div | Lt | Le | Gt | Ge, _, _) if isValue(e1) => Binary(bop, e1, step(e2))
        case _ => Binary(bop, step(e1), e2)
      }

      case If(e1, e2, e3) => If(step(e1), e2, e3)
      case ConstDecl(x, e1, e2) => ConstDecl(x, step(e1), e2)
      case Print(e1) => Print(step(e1))

      case Call(e1, e2) => (e1, e2) match {
        case (N(_) | B(_) | S(_) | Undefined, _) => throw DynamicTypeError(e)
        case (Function(_, _, _), _) => Call(e1, step(e2))
        case _ => Call(step(e1), e2)
      }

      /* Cases that should never match. Your cases above should ensure this. */
      case Var(_) => throw new AssertionError("Gremlins: internal error, not closed expression.")
      case N(_) | B(_) | Undefined | S(_) | Function(_, _, _) => throw new AssertionError("Gremlins: internal error, step should not be called on values.");
    }
  }


  /* External Interfaces */
  
//  this.debug = true // uncomment this if you want to print debugging information
  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file

}
