package problems.symdiff;

import lombok.experimental.UtilityClass;
import lombok.val;

import static problems.util.sexp.SExpression.*;

/**
 * Java/Lisp hybrid symbolic differentation demo.
 * This shows how to write in lisp if you really want to but want to stick to java.
 *
 * Adopted lisp example from https://github.com/aksiazek/symbolic-differentiation/blob/master/symbolic-derivation.lisp
 */
@UtilityClass public class SymbolicDifferentiationDemo {

  public static Node notIn(Node var, Node expr) {
    if (expr instanceof Cons) {
      final Cons c = (Cons) expr;
      if (c.getCar() instanceof Cons) {
        return notIn(var, c.getCar());
      } else if (c.getCar().equals(var)) {
        return NIL;
      }

      return notIn(var, c.getCdr());
    }

    return T;
  }

  public static Node rewrite(Node expr) {
    if (!(expr instanceof Cons)) {
      return expr;
    }

    val operator = car(expr);
    val arg1 = car(cdr(expr));
    val arg2 = car(cdr(cdr(expr)));

    if (operator == sym("+")) {
      if (NIL == arg2) {
        return rewrite(arg1);
      } else if (T == equalsp(arg1, imm(0))) {
        return arg2;
      } else if (T == equalsp(arg2, imm(0))) {
        return arg1;
      } else if (T == numberp(arg1) && T == numberp(arg2)) {
        return biop((a, b) -> (a + b), arg1, arg2);
      }
      return expr;
    }

    if (operator == sym("*")) {
      if (T == equalsp(arg1, imm(0)) || T == equalsp(arg2, imm(0))) {
        return imm(0);
      }
      if (T == equalsp(arg2, imm(1))) {
        return arg1;
      }
      if (T == equalsp(arg1, imm(1))) {
        return arg2;
      }
      if (T == numberp(arg1) && T == numberp(arg2)) {
        return biop((a, b) -> (a * b), arg1, arg2);
      }
      return expr;
    }

    if (operator == sym("/")) {
      if (T == equalsp(arg2, imm(0))) {
        throw new IllegalArgumentException("division by zero");
      }
      if (T == equalsp(arg2, imm(0))) {
        return imm(0);
      }
      if (T == equalsp(arg1, imm(1))) {
        return arg2;
      }
      if (T == numberp(arg1) && T == numberp(arg2)) {
        return biop((a, b) -> (a / b), arg1, arg2);
      }
      return expr;
    }

    if (operator == sym("^")) {
      if (T == equalsp(arg2, imm(0))) {
        return imm(1);
      }
      if (T == equalsp(arg2, imm(1))) {
        return arg1;
      }
      if (T == numberp(arg1) && T == numberp(arg2)) {
        return biop(Math::pow, arg1, arg2);
      }
    }

    return expr;
  }

  public static Node isNamedFunction(Node name) {
    return memberp(name, list(sym("^"), sym("sin"), sym("cos"), sym("tg"), sym("ctg"), sym("sqrt"),
        sym("exp"), sym("ln"), sym("log"), sym("asin"), sym("acos"), sym("atg"), sym("actg")));
  }

  public static Node namedFunctionDerivative(Node name, Node arg) {
    if (sym("sin") == name) {
      return list(sym("cos"), rewrite(arg));
    } else if (sym("cos") == name) {
      return list(sym("-"), list(sym("sin"), rewrite(arg)));
    } else if (sym("tg") == name) {
      return list(sym("+"), imm(1),
          list(sym("^"), list(sym("tg"), rewrite(arg)), imm(2)));
    } else if (sym("ctg") == name) {
      return list(sym("-"), list(sym("+"), imm(1),
          list(sym("^"), list(sym("ctg"), rewrite(arg)), imm(2))));
    } else if (sym("sqrt") == name) {
      return list(sym("/"), imm(1), list(sym("*"), imm(2), list(sym("sqrt"), rewrite(arg))));
    } else if (sym("exp") == name) {
      return rewrite(list(sym("exp"), rewrite(arg)));
    } else if (sym("ln") == name) {
      return list(sym("/"), imm(1), rewrite(arg));
    } else if (sym("log") == name) {
      return list(sym("/"), imm(1), list(sym("*"), rewrite(arg), list(sym("ln"), imm(10))));
    } else if (sym("asin") == name) {
      return list(sym("/"), imm(1), list(sym("sqrt"),
          list(sym("-"), imm(1), list(sym("^"), rewrite(arg), imm(2)))));
    } else if (sym("acos") == name) {
      return list(sym("-"), list(sym("/"), imm(1), list(sym("sqrt"),
          list(sym("-"), imm(1), list(sym("^"), rewrite(arg), imm(2))))));
    } else if (sym("atg") == name) {
      return list(sym("/"), imm(1),
          list(sym("+"), imm(1), list(sym("^"), rewrite(arg), imm(2))));
    } else if (sym("actg") == name) {
      return list(sym("-"), list(sym("/"), imm(1),
          list(sym("+"), imm(1), list(sym("^"), rewrite(arg), imm(2)))));
    }

    return NIL;
  }

  public static Node pow(Node var, Node arg1, Node arg2) {
    // a^f(x)
    if (T == notIn(var, arg1)) {
      return rewrite(list(sym("*"),
          rewrite(list(sym("*"),
              rewrite(list(sym("^"), arg1, arg2)),
              list(sym("ln"), arg1))),
          derive(var, arg2)));
    }

    // f(x)^a
    if (T == notIn(var, arg2)) {
      return rewrite(list(sym("*"),
          rewrite(list(sym("*"), arg2,
              rewrite(list(sym("^"), arg1,
                  rewrite(list(sym("-"), arg2, imm(1))))),
              derive(var, arg1)))));
    }

    // f(x)^g(x)
    return derive(var, list(sym("exp"), rewrite(list(sym("*"), arg2, list(sym("ln"), arg1)))));
  }

  public static Node derive(Node var, Node expr) {
    if (NIL == expr) {
      return NIL;
    }

    if ((!expr.isCons()) && T == equalsp(var, expr)) {
      return imm(1);
    }

    if (T == notIn(var, expr)) {
      return imm(0);
    }

    val operator = car(expr);
    val arg1 = rewrite(car(cdr(expr)));
    val arg2 = rewrite(car(cdr(cdr(expr))));

    if (T == memberp(operator, list(sym("+"), sym("-")))) {
      if (NIL == arg2) {
        return rewrite(list(operator, derive(var, arg1)));
      }
      return rewrite(list(operator, derive(var, arg1), derive(var, arg2)));
    }

    if (sym("*") == operator) {
      return rewrite(list(sym("+"),
          rewrite(list(sym("*"), derive(var, arg1), arg2)),
          rewrite(list(sym("*"), arg1, derive(var, arg2)))));
    }

    if (T == equalsp(operator, sym("/"))) {
      return rewrite(list(sym("/"),
          rewrite(list(sym("-"),
              rewrite(list(sym("*"), derive(var, arg1), arg2)),
              rewrite(list(sym("*"), arg1, derive(var, arg2))))),
          rewrite(list(sym("^"), arg2, imm(2)))));
    }

    if (sym("^") == operator) {
      return pow(var, arg1, arg2);
    }

    if (T == isNamedFunction(operator)) {
      return rewrite(list(sym("*"), namedFunctionDerivative(operator, arg1), derive(var, arg1)));
    }

    throw new IllegalArgumentException("Unknown function=" + operator);
  }

  public static void main(String[] args) {
    System.out.println(derive(sym("x"), parseSimple("(+ x 1)")));
    System.out.println(derive(sym("x"), parseSimple("(sin (sqrt x))")));
  }
}
