package simplifier

import AST._

// to implement
// avoid one huge match of cases
// take into account non-greedy strategies to resolve cases with power laws
object Simplifier {

  /*
  * Default function to call for simplification of any node
  * */
  def simplify(node: Node): Node = {
    NodeList(List(simplifyNode(node).orNull))
  }

  def getOrEmpty(node: Option[Node]) = {
    node.getOrElse(NodeList(List()))
  }

  def simplifyNode(node: Node): Option[Node] = node match {
    //      Lists
    case n @ NodeList(_) => simplifyNodeList(n)
    case l @ ElemList(_) => simplifyElemList(l)
    case t @ Tuple(_) => simplifyTuple(t)
    //      Function and lambda
    case f @ FunDef(_, _, _) => simplifyFunDef(f)
    case f @ FunCall(_, _) => simplifyFunCall(f)
    case f @ LambdaDef(_, _) => simplifyLambdaDef(f)
    //      Conditional blocks
    case i @ IfElseInstr(nodes, right) => evaluateConditions(simplifyList(nodes), simplifyNode(right))
    case i @ IfElifInstr(nodes) => evaluateConditions(simplifyList(nodes))
    case i @ IfInstr(_, _) => simplifyIf(i)
    case i @ ElifInstr(_, _) => simplifyElif(i)
    case i @ IfElseExpr(_, _, _) => simplifyIfElse(i)
    //      Loops
    case i @ WhileInstr(_, _) => simplifyWhile(i)
    //      Maps
    case m @ KeyDatumList(_) => simplifyMap(m)
    //      Accessors
    case a @ GetAttr(expr, attr) => Some(GetAttr(simplifyNode(expr).get, attr))
    case a @ Subscription(expr, sub) => Some(Subscription(simplifyNode(expr).get, simplifyNode(sub).get))
    //      Assignment
    case a @ Assignment(_, _) => simplifyAssignment(a)
    //      Expressions
    case e @ BinExpr(_, _, _) => simplifyBinExpr(e)
    case e @ Unary(_, _) => simplifyUnary(e)
    //      Other
    case i @ PrintInstr(expr) => Some(PrintInstr(getOrEmpty(simplifyNode(expr))))
    //      Default
    case _ => Some(node)
  }

  /*
  * Nodes containing lists of nodes
  * -------------------------------
  *
  * Simplify every node in the list
  */

  def simplifyList(nodes: List[Node]): List[Node] = nodes.flatMap(simplifyNode)

  /*
  * Returns:
  *   1. Nothing if resulting list is empty
  *   2. Node if list contains single node
  *   3. Modified list otherwise
  * */
  def simplifyNodeList(n: NodeList): Option[Node] =
    removeDeadAssignments(simplifyList(n.list)) match {
      case List() => None
      case List(expr) => Some(expr)
      case list => Some(NodeList(list))
    }

  def simplifyElemList(l: ElemList): Option[Node] = Some(ElemList(simplifyList(l.list)))

  def simplifyTuple(t: Tuple): Option[Node] = Some(Tuple(simplifyList(t.list)))

  /*
  * Functions
  * ---------
  * */

  //  Simplify function body
  def simplifyFunDef(f: FunDef): Option[Node] =
    Some(FunDef(f.name, f.formal_args, getOrEmpty(simplifyNode(f.body))))

  def simplifyLambdaDef(f: LambdaDef): Option[Node] =
    Some(LambdaDef(f.formal_args, getOrEmpty(simplifyNode(f.body))))

  //  Simplify argument expressions in function call
  def simplifyFunCall(f: FunCall): Option[Node] =
    Some(FunCall(f.name, getOrEmpty(simplifyNode(f.args_list))))


  /*
  * Conditional blocks
  * ------------------
  * Simplify condition and body
  * */
  def simplifyIf(i: IfInstr): Option[Node] =
    Some(IfInstr(simplifyNode(i.cond).get, getOrEmpty(simplifyNode(i.left))))

  def simplifyElif(i: ElifInstr): Option[Node] =
    Some(ElifInstr(simplifyNode(i.cond).get, getOrEmpty(simplifyNode(i.left))))

  def simplifyIfElse(i: IfElseExpr): Option[Node] = {
    val cond = simplifyNode(i.cond).get
    val left = getOrEmpty(simplifyNode(i.left))
    val right = getOrEmpty(simplifyNode(i.right))
    cond match {
      case TrueConst() => Some(left)
      case FalseConst() => Some(right)
      case _ => Some(IfElseExpr(cond, left, right))
    }
  }

  // Checks for known conditions
  def evaluateConditions(nodes: List[Node], right: Option[Node] = None): Option[Node] = {

    def allFalse() = nodes.forall {
      case IfInstr(cond, expr) if cond.equals(FalseConst()) => true
      case ElifInstr(cond, expr) if cond.equals(FalseConst()) => true
      case _ => false
    }

    nodes match {
      case IfInstr(cond, expr) :: tail if cond.equals(TrueConst()) => Some(expr)
      case ElifInstr(cond, expr) :: tail if cond.equals(TrueConst()) => Some(expr)
      case head :: tail => evaluateConditions(tail, right)
      case Nil =>
        if (allFalse())
          right
        else right match {
          case Some(node) => Some(IfElseInstr(nodes, node))
          case None => Some(IfElifInstr(nodes))
        }
    }
  }


  /*
  * Loops
  * -----
  * Simplify loop body and check for known condition
  * */
  def simplifyWhile(i: WhileInstr): Option[Node] = {
    val cond = simplifyNode(i.cond).get
    val body = simplifyNode(i.body)
    if (cond.equals(FalseConst()))
      None
    else body match {
      case Some(node) => Some(WhileInstr(cond, node))
      case None => None
    }
  }


  /*
  * Assignments
  * -----------
  * */

  // Checks for sequential assignments to same variable
  def removeDeadAssignments(nodes: List[Node]): List[Node] = nodes match {
    case Nil => nodes
    case head :: Nil => nodes
    case head :: tail => (head, tail.head) match {
      case (Assignment(x, _), a @ Assignment(y, _)) if x.equals(y) => a :: removeDeadAssignments(tail.drop(1))
      case _ => head :: removeDeadAssignments(tail)
    }
  }

  def simplifyAssignment(a: Assignment): Option[Node] = {
    val left = simplifyNode(a.left).get
    val right = simplifyNode(a.right).orNull
    (left, right) match {
      // Empty assignment
      case (x, null) => None
      // No effect instructions
      case (x, y) if x.equals(y) => None
      case _ => Some(Assignment(left, right))
    }
  }


  /*
  * Maps
  * ----
  * Simplify values and remove duplicate keys
  * */

  def simplifyMap(m: KeyDatumList): Option[Node] = {
    Some(KeyDatumList(
      m.list
        .map(datum => datum.key)
        .distinct
        .map(key => KeyDatum(key, m.list.reverse
          .find(datum => datum.key.equals(key)).get.key))
        .map(datum => KeyDatum(datum.key, simplifyNode(datum.value).get))
    ))
  }


  /*
  * Binary expressions
  * ------------------
  * */

  def simplifyBinExpr(e: BinExpr): Option[Node] = {

    def simplifyArithmeticExpr(op: String, left: Node, right: Node): Option[Node] = {

      val negOp = Map("+" -> "-", "-" -> "+")

      (op, left, right) match {
        // Replace unary minus with binary when used in addition
        case ("+", Unary("+", x), y) => simplifyNode(BinExpr("+", x, y))
        case ("+", Unary("-", x), y) => simplifyNode(BinExpr("-", y, x))
        // Simplify addition and subtraction of 0
        case ("+" | "-", x, IntNum(n)) if n == 0 => Some(x)
        case ("-", IntNum(n), x) if n == 0 => simplifyNode(Unary("-", x))
        // Simplify subtraction of equal values
        case ("-", x, y) if x.equals(y) => Some(IntNum(0))
        case ("+" | "-", BinExpr("*", l, r), x) if l.equals(x) =>
          simplifyNode(BinExpr("*", l, BinExpr(op, r, IntNum(1))))
        case ("+" | "-", BinExpr("*", l1, r1), BinExpr("*", l2, r2)) if l1.equals(l2) =>
          simplifyNode(BinExpr("*", l1, BinExpr(op, r1, r2)))
        case ("+" | "-", BinExpr("*", l1, r1), BinExpr("*", l2, r2)) if r1.equals(r2) =>
          simplifyNode(BinExpr("*", r1, BinExpr(op, l1, l2)))
        case ("*" | "/", x, IntNum(n)) if n == 1 => Some(x)
        case ("*", IntNum(n), x) if n == 0 => Some(IntNum(0))
        case ("*", BinExpr("**", x1, y), BinExpr("**", x2, z))
          if x1.equals(x2) => Some(BinExpr("**", x1, simplifyNode(BinExpr("+", y, z)).get))
        case ("/", x, y) if x.equals(y) => Some(IntNum(1))
        case ("/", left, BinExpr("/", x, y))
          if left.equals(x) => simplifyNode(y)
        case ("*", x, BinExpr("/", IntNum(n), y))
          if n == 1 => simplifyNode(BinExpr("/", x, y))
        case _ => Some(BinExpr(op, left, right))
      }
    }

    def simplifyBooleanExpr(op: String, left: Node, right: Node): Node = (op, left, right) match {
      case ("or" | "and", x, y) if x.equals(y) => x
      case ("or", x, TrueConst()) => TrueConst()
      case ("or", x, FalseConst()) => x
      case ("and", x, TrueConst()) => x
      case ("and", x, FalseConst()) => FalseConst()
      case _ => BinExpr(op, left, right)
    }

    def simplifyComparison(op: String, left: Node, right: Node): Node = (op, left, right) match {
      case ("==" | ">=" | "<=", x, y) if x.equals(y) => TrueConst()
      case ("!=" | ">" | "<", x, y) if x.equals(y) => FalseConst()
      case _ => BinExpr(op, left, right)
    }

    def calculateExpr(op: String, left: Node, right: Node): Node = {

      val aOps = List("+", "-", "*", "/", "**", "%")
      val bOps = List(">=", "<=", "==", "!=", "<", ">")

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

    def concatTuples(t1: Tuple, t2: Tuple) = Tuple(t1.list.flatMap(simplifyNode) ++ t2.list.flatMap(simplifyNode))

    def concatLists(l1: ElemList, l2: ElemList) = ElemList(l1.list.flatMap(simplifyNode) ++ l2.list.flatMap(simplifyNode))

    def simplifyExpr(e: BinExpr): Option[Node] = {
      val op = e.op
      val tmpLeft = simplifyNode(e.left)
      val tmpRight = simplifyNode(e.right)

      val left = getOrEmpty(tmpLeft)
      val right = getOrEmpty(tmpRight)

      if (left == null || left.equals(NodeList(List()))) return tmpRight
      if (right == null || right.equals(NodeList(List()))) return tmpLeft

      val f = BinExpr(op, left, right)

      def chooseStrategy(f: BinExpr) =
        f match {
          case BinExpr(_, (IntNum(_) | FloatNum(_)), (IntNum(_) | FloatNum(_))) => Some(calculateExpr(f.op, f.left, f.right))
          case BinExpr("+", t1 @ Tuple(_), t2 @ Tuple(_)) => Some(concatTuples(t1, t2))
          case BinExpr("+", l1 @ ElemList(_), l2 @ ElemList(_)) => Some(concatLists(l1, l2))
          case BinExpr("+" | "-" | "*" | "/", _, _) => simplifyArithmeticExpr(f.op, f.left, f.right)
          case BinExpr("or" | "and", _, _) => Some(simplifyBooleanExpr(f.op, f.left, f.right))
          case BinExpr(">=" | "<=" | "==" | "!=" | "<" | ">", _, _) => Some(simplifyComparison(f.op, f.left, f.right))
          case _ => Some(e)
        }

      def checkCommutativity(e: BinExpr) =
        e.left match {
          case f @ BinExpr(o, _, _) if BinExpr.commutative.contains(o) =>
            val simple = chooseStrategy(BinExpr(e.op, e.left, e.right))
            val simpleR = chooseStrategy(BinExpr(e.op, getOrEmpty(simplifyNode(reverse(f))), e.right))
            if (getOrEmpty(simple).equals(e) && !getOrEmpty(simpleR).equals(e)) simpleR
            else simple
          case _ => chooseStrategy(BinExpr(e.op, e.left, e.right))
        }

      val simple = checkCommutativity(f)
      getOrEmpty(simple) match {
        case BinExpr(op, left, right) =>
          left match {
            case e @ BinExpr(o, x, y) if Priority.binary(o) <= Priority.binary(op) =>
              val subR = BinExpr(op, x, right)
              val simpleR = getOrEmpty(checkCommutativity(subR))
              if (!simpleR.equals(subR))
                checkCommutativity(BinExpr(o, simpleR, y))
              else {
                val subL = BinExpr(op, Unary(o, y), right)
                val simpleL = getOrEmpty(checkCommutativity(subL))
                if (!simpleL.equals(subL))
                  checkCommutativity(BinExpr("+", x, simpleL))
                else
                  simple
              }
            case _ => simple
          }
        case _ => simple
      }
    }


    def reverse(e: BinExpr): BinExpr = e match {
      case BinExpr(op, left, right) => BinExpr(op, right, left)
    }

    if (BinExpr.commutative.contains(e.op)) {
      val simple = simplifyExpr(e)
      val simpleR = simplifyExpr(reverse(e))
      if (getOrEmpty(simple).equals(e) && !getOrEmpty(simpleR).equals(e)) simpleR
      else simple
    }
    else simplifyExpr(e)
  }

  def simplifyUnary(e: Unary): Option[Node] = {

    val op = e.op
    val expr = e.expr

    val ops = List(">=", "<=", "==", "!=", "<", ">")
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
      case ("not", c @ (TrueConst() | FalseConst())) => Some(negate(c))
      case ("not", e @ BinExpr(o, l, r)) if ops.contains(o) => Some(negate(e))
      case (op1, Unary(op2, x)) if op1 == op2 => simplifyNode(x)
      case _ =>
        val node = simplifyNode(expr)
        node match {
          case Some(n) =>
            val e = Unary(op, n)
            if (e.expr != expr)
              simplifyUnary(e)
            else
              Some(e)
          case _ => None
        }

    }
  }

}
