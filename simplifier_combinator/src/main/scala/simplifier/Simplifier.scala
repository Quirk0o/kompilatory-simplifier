package simplifier

import AST._

// to implement
// avoid one huge match of cases
// take into account non-greedy strategies to resolve cases with power laws
object Simplifier {

  def simplify(node: Node): Node = node match {
    case NodeList(list) => NodeList(list.map(simplify))
    case m @ KeyDatumList(_) => simplifyMap(m)
    case a @ Assignment(_, _, _) => simplifyAssignment(a)
    case e @ BinExpr(_, _, _) => simplifyBinExpr(e)
    case e @ Unary(_, _) => simplifyUnary(e)
    case _ => node
  }

  def simplifyAssignment(a: Assignment): Option[Node] = (a.left, a.right) match {
    case (x, y) if x.equals(y) => None
    case _ => Some(a)
  }

  def simplifyMap(m: KeyDatumList): Node = {
    KeyDatumList(
      m.list
        .map(datum => datum.key)
        .distinct
        .map(key => KeyDatum(key, m.list.reverse
          .find(datum => datum.key.equals(key)).get.key))
        .map(datum => KeyDatum(datum.key, simplify(datum.value)))
    )
  }

  def simplifyBinExpr(e: BinExpr): Node = {

    def reverse(e: BinExpr): BinExpr = e match { case BinExpr(op, left, right) => BinExpr(op, right, left) }

    def simplifyArithmeticExpr(op: String, left: Node, right: Node): Node = (op, left, right) match {
      case ("+", Unary("-", x), y)              => simplify(BinExpr("-", y, x))
      case ("+" | "-", x, IntNum(n)) if n == 0  => x
      case ("-", IntNum(n), x) if n == 0        => simplify(Unary("-", x))
      case ("-", x, y) if x.equals(y)           => IntNum(0)
      case ("*" | "/", x, IntNum(n)) if n == 1  => x
      case ("*", IntNum(n), x) if n == 0        => IntNum(0)
      case ("*", BinExpr("**", x1, y),
                 BinExpr("**", x2, z))
        if x1.equals(x2)                        => BinExpr("**", x1, simplify(BinExpr("+", y, z)))
      case ("/", x, y) if x.equals(y)           => IntNum(1)
      case ("/", left, BinExpr("/", x, y))
        if left.equals(x)                       => simplify(y)
      case ("*", x, BinExpr("/", IntNum(n), y))
        if n == 1                               => simplify(BinExpr("/", x, y))
      case _ => BinExpr(op, left, right)
    }

    def simplifyBooleanExpr(op: String, left: Node, right: Node): Node = (op, left, right) match {
      case ("or" | "and", x, y) if x.equals(y)  => x
      case ("or", x, TrueConst())               => TrueConst()
      case ("or", x, FalseConst())              => x
      case ("and", x, TrueConst())              => x
      case ("and", x, FalseConst())             => FalseConst()
      case _ => BinExpr(op, left, right)
    }

    def simplifyComparison(op: String, left: Node, right: Node): Node = (op, left, right) match {
      case ("==" | ">=" | "<=", x, y) if x.equals(y) => TrueConst()
      case ("!=" | ">" | "<", x, y) if x.equals(y) => FalseConst()
      case _ => BinExpr(op, left, right)
    }

    def calculateExpr(op: String, left: Node, right: Node): Node = {

      val aOps = List("+","-","*","/","**","%")
      val bOps = List(">=","<=","==","!=","<",">")

      def calculate(x: Number, y: Number): Number = aFunMap(op)(x, y)
      def compare(x: Number, y: Number): Boolean = bFunMap(op)(x, y)

      def aFunMap = Map(
        "+" -> ((x: Number, y: Number) => x.doubleValue() + y.doubleValue()),
        "-" -> ((x: Number, y: Number) => x.doubleValue() - y.doubleValue()),
        "*" -> ((x: Number, y: Number) => x.doubleValue() * y.doubleValue()),
        "/" -> ((x: Number, y: Number) => x.doubleValue() / y.doubleValue()),
        "**" -> ((x: Number, y: Number) => Math.pow(x.doubleValue(), y.doubleValue())),
        "%" -> ((x: Number, y: Number) => x.doubleValue() % y.doubleValue())
      )

      def bFunMap = Map(
        ">=" -> ((x: Number, y: Number) => x.doubleValue() >= y.doubleValue()),
        "<=" -> ((x: Number, y: Number) => x.doubleValue() <= y.doubleValue()),
        "==" -> ((x: Number, y: Number) => x.doubleValue() == y.doubleValue()),
        "!=" -> ((x: Number, y: Number) => x.doubleValue() != y.doubleValue()),
        "<" -> ((x: Number, y: Number) => x.doubleValue() < y.doubleValue()),
        ">" -> ((x: Number, y: Number) => x.doubleValue() > y.doubleValue())
      )

      if (aOps.contains(op)) {
        (op, left, right) match {
          case ("/", IntNum(x), IntNum(y)) => FloatNum(calculate(x, y).doubleValue())
          case (_, IntNum(x), IntNum(y)) => IntNum(calculate(x, y).intValue())
          case (_, FloatNum(x), FloatNum(y)) => FloatNum(calculate(x, y).doubleValue())
          case (_, IntNum(x), FloatNum(y)) => FloatNum(calculate(x, y).doubleValue())
          case (_, FloatNum(x), IntNum(y)) => FloatNum(calculate(x, y).doubleValue())
          case _ => throw new IllegalArgumentException()
        }
      }
      else if (bOps.contains(op)) {
        var a, b = 0.0
        left match {
          case IntNum(x) => a = x.doubleValue()
          case FloatNum(x) => a = x
          case _ => throw new IllegalArgumentException()
        }
        right match {
          case IntNum(x) => b = x.doubleValue()
          case FloatNum(x) => b = x
          case _ => throw new IllegalArgumentException()
        }

        compare(a, b) match {
          case true => TrueConst()
          case false => FalseConst()
        }
      }
      else throw new IllegalArgumentException()
    }

    def concatTuples(t1: Tuple, t2: Tuple) = Tuple(t1.list.map(simplify) ++ t2.list.map(simplify))

    def concatLists(l1: ElemList, l2: ElemList) = ElemList(l1.list.map(simplify) ++ l2.list.map(simplify))

    def simplifyExpr(e: BinExpr) = {
      val f = BinExpr(e.op, simplify(e.left), simplify(e.right))

      f match {
        case BinExpr(_, (IntNum(_) | FloatNum(_)), (IntNum(_) | FloatNum(_))) => calculateExpr(f.op, f.left, f.right)
        case BinExpr("+", t1@Tuple(_), t2@Tuple(_)) => concatTuples(t1, t2)
        case BinExpr("+", l1 @ ElemList(_), l2 @ ElemList(_)) => concatLists(l1, l2)
        case BinExpr("+" | "-" | "*" | "/", _, _) => simplifyArithmeticExpr(f.op, f.left, f.right)
        case BinExpr("or" | "and", _, _) => simplifyBooleanExpr(f.op, f.left, f.right)
        case BinExpr(">=" | "<=" | "==" | "!=" | "<" | ">", _, _) => simplifyComparison(f.op, f.left, f.right)
        case _ => f
      }
    }

    if (BinExpr.commutative.contains(e.op)) {
      val reversed = simplifyExpr(reverse(e))
      val simplified = simplifyExpr(e)
      if (simplified.equals(e)) reversed
      else simplified
    }
    else
      simplifyExpr(e)
  }

  def simplifyUnary(e: Unary): Node = {

    val op = e.op
    val expr = e.expr

    val ops = List(">=","<=","==","!=","<",">")
    val opMap = Map(
      ">=" -> "<",
      "<=" -> ">",
      "==" -> "!=",
      "!=" -> "==",
      "<" -> ">=",
      ">" -> "<="
    )

    def negate(node: Node): Node = node match {
      case TrueConst() => FalseConst()
      case FalseConst() => TrueConst()
      case BinExpr(o, l, r) => BinExpr(opMap(o), l, r)
      case _ => throw new IllegalArgumentException()
    }

    (op, expr) match {
      case ("not", c@(TrueConst() | FalseConst())) => negate(c)
      case ("not", e@BinExpr(o, l, r)) if ops.contains(o) => negate(e)
      case (op1, Unary(op2, x)) if op1 == op2 => simplify(x)
      case _ =>
        val e = Unary(op, simplify(expr))
        if (e.expr != expr)
          simplifyUnary(e)
        else
          e
    }
  }

}
