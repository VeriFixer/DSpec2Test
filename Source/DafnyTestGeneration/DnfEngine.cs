using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Expr = Microsoft.Boogie.Expr;

namespace DafnyTestGeneration {

  public static class DnfEngine {

    /// <summary>
    /// Decomposes a Boogie Expr into Disjunctive Normal Form (DNF) 
    /// Returns a list of conjunctive clauses (each clause is a list of Expr).
    /// </summary>
    public static List<List<Expr>> ExprToDnf(Expr expr) {
      return ExprToDnfInner(expr);
    }
    
    /// <summary>
    /// Build a left-folded conjunction (And) of multiple expressions.
    /// </summary>
    public static Expr ConjoinExprs(List<Expr> exprs) {
      if (exprs.Count == 0) {
        return Expr.True;
      }
      var result = exprs[0];
      for (int i = 1; i < exprs.Count; i++) {
        result = Expr.And(result, exprs[i]);
      }
      return result;
    }
    
    /// <summary>
    /// Calculates the safe DNF combination of a List of Expr
    /// </summary>
    public static List<List<Expr>> CalculateSafeCombinations(List<Expr> exprs) {
      var result = new List<List<Expr>>{ new() };

      foreach (var expr in exprs) {
        var exprDnf = ExprToDnf(expr);
        var tmpDnfExprs = new List<List<Expr>>();
        var combinations = new List<List<Expr>>();
        var previousNegations = new List<Expr>();

        for (int i = 0; i < exprDnf.Count; i++) {
          var combination = new List<Expr>();
          var currentBranch = exprDnf[i];
          
          combination.AddRange(previousNegations);
          combination.AddRange(currentBranch);
          
          if (!FindContradiction(combination)) {
            combinations.Add(combination);
          }
          
          if (currentBranch.Count == 1) {
            previousNegations.Add(Negate(currentBranch[0]));
          } else if (currentBranch.Count > 1) {
            var conjoined = ConjoinExprs(currentBranch);
            previousNegations.Add(Negate(conjoined));
          }
        }

        foreach (var existingCombination in result) {
          foreach (var comb in combinations) {
            var merged = new List<Expr>(existingCombination);
            merged.AddRange(comb);

            if (!FindContradiction(merged)) {
              tmpDnfExprs.Add(merged);
            }
          }
        }
        result = tmpDnfExprs;
      }
      
      return result;
    }

    /// <summary>
    /// Calculates the full DNF combination of a List of Expr
    /// </summary>
    public static List<List<Expr>> CalculateAllCombinations(List<Expr> exprs) {
      var result = new List<List<Expr>>{ new() };

      foreach (var expr in exprs) {
        var exprDnf = ExprToDnf(expr);
        var tmpDnfExprs = new List<List<Expr>>();
        
        var knownUnsatMasks = new List<int>();
        int pm = exprDnf.Count;
        int totalComb = (1 << pm) - 1;
        var combinations = new List<List<Expr>>();

        for (int mask = 1; mask <= totalComb; mask++) {
          if (knownUnsatMasks.Any(unsatMask => (mask & unsatMask) == unsatMask)) {
            continue;
          }

          var combination = new List<Expr>();
          for (int bit = 0; bit < pm; bit++) {
            var currentBranch = exprDnf[bit];
            if ((mask & (1 << bit)) != 0) {
              combination.AddRange(currentBranch);
            } else {
              if (currentBranch.Count == 1) {
                combination.Add(Negate(currentBranch[0]));
              } else if (currentBranch.Count > 1) {
                var conjoined = ConjoinExprs(currentBranch);
                combination.Add(Negate(conjoined));
              }
            }
          }

          if (FindContradiction(combination)) {
            knownUnsatMasks.Add(mask);
            continue;
          }
          combinations.Add(combination);
        }

        foreach (var existingCombination in result) {
          foreach (var comb in combinations) {
            var merged = new List<Expr>(existingCombination);
            merged.AddRange(comb);

            if (!FindContradiction(merged)) {
              tmpDnfExprs.Add(merged);
            }
          }
        }
        result = tmpDnfExprs;
      }
      
      return result;
    }

    /// <summary>
    /// Calculate the cross product of two lists of expressions.
    /// Each clause from A is merged with each clause from B.
    /// </summary>
    private static List<List<Expr>> CrossProduct(List<List<Expr>> a, List<List<Expr>> b) {
      var result = new List<List<Expr>>();
      foreach (var clauseA in a) {
        foreach (var clauseB in b) {
          var merged = new List<Expr>(clauseA);
          merged.AddRange(clauseB);
          result.Add(merged);
        }
      }
      return result;
    }

    /// <summary>
    /// Wraps an expression in a negation: !(expr)
    /// If the expression is already negative, it returns its positive counterpart
    /// </summary>
    private static Expr Negate(Expr expr) {
      if (expr is NAryExpr { Fun: UnaryOperator { Op: UnaryOperator.Opcode.Not } } nary) {
        return nary.Args[0];
      }
      return Expr.Not(expr);
    }

    /// <summary>
    /// Inner workings of the DNF decomposition
    /// </summary>
    private static List<List<Expr>> ExprToDnfInner(Expr expr, bool negated = false) {
      if (expr is NAryExpr nary) {
        if (nary.Fun is UnaryOperator { Op: UnaryOperator.Opcode.Not }) {
          return ExprToDnfInner(nary.Args[0], !negated);
        }
        
        if (nary.Fun is BinaryOperator binOp) {
          var a = nary.Args[0];
          var b = nary.Args[1];

          switch (binOp.Op) {
            case BinaryOperator.Opcode.Imp when !negated: {
              var notA = ExprToDnfInner(a, true);
              var bDnf = ExprToDnfInner(b);
              var result = new List<List<Expr>>(notA);
              result.AddRange(bDnf);
              return result;
            }
            case BinaryOperator.Opcode.Imp: {
              return CrossProduct(ExprToDnfInner(a), ExprToDnfInner(b, true));
            }
            case BinaryOperator.Opcode.And when !negated: {
              return CrossProduct(ExprToDnfInner(a), ExprToDnfInner(b));
            }
            case BinaryOperator.Opcode.And: {
              var notA = ExprToDnfInner(a, true);
              var notB = ExprToDnfInner(b, true);
              var result = new List<List<Expr>>(notA);
              result.AddRange(notB);
              return result;
            }
            case BinaryOperator.Opcode.Or when !negated: {
              var aDnf = ExprToDnfInner(a);
              var bDnf = ExprToDnfInner(b);
              var result = new List<List<Expr>>(aDnf);
              result.AddRange(bDnf);
              return result;
            }
            case BinaryOperator.Opcode.Or: {
              return CrossProduct(ExprToDnfInner(a, true), ExprToDnfInner(b, true));
            }
            case BinaryOperator.Opcode.Iff when !negated: {
              var ab = CrossProduct(ExprToDnfInner(a), ExprToDnfInner(b));
              var notAnotB = CrossProduct(ExprToDnfInner(a, true), ExprToDnfInner(b, true));
              var result = new List<List<Expr>>(ab);
              result.AddRange(notAnotB);
              return result;
            }
            case BinaryOperator.Opcode.Iff: {
              var aNotB = CrossProduct(ExprToDnfInner(a), ExprToDnfInner(b, true));
              var notAb = CrossProduct(ExprToDnfInner(a, true), ExprToDnfInner(b));
              var result = new List<List<Expr>>(aNotB);
              result.AddRange(notAb);
              return result;
            }
          }
        }
      }
      else if (expr is ExistsExpr exists && !negated) {
        var bodyDnf = ExprToDnfInner(exists.Body);
        var result = new List<List<Expr>>();
        foreach (var branch in bodyDnf) {
          var conjoined = ConjoinExprs(branch);
          result.Add([
            new ExistsExpr(exists.tok, exists.TypeParameters, exists.Dummies, exists.Attributes, exists.Triggers,
              conjoined)
          ]);
        }
        return result;
      }
      else if (expr is ForallExpr forall && negated) {
        var bodyDnf = ExprToDnfInner(forall.Body, true);
        var result = new List<List<Expr>>();
        foreach (var branch in bodyDnf) {
          var conjoined = ConjoinExprs(branch);
          result.Add([
            new ExistsExpr(forall.tok, forall.TypeParameters, forall.Dummies, forall.Attributes, forall.Triggers,
              conjoined)
          ]);
        }
        return result;
      }
     
      var atom = negated ? Negate(expr) : expr;
      return [[atom]];
    }

    /// <summary>
    /// Finds contradictions in a DNF combination, making the conjunction trivially UNSAT without needing Z3.
    /// Detects:
    ///   1. Direct complements: L and !(L) both present
    ///   2. Equality contradictions: x == v1 and x == v2 where v1 != v2 (and v1 and v2 are numeric)
    ///   2. Inequality contradictions: e.g., x lt 0 and x gt 0, or x == 0 and x != 0
    /// Returns true if a contradiction is found, and false otherwise.
    /// </summary>
    public static bool FindContradiction(List<Expr> combination) {
      var equalities = new Dictionary<string, double>();
      var inequalities = new Dictionary<string, double>();
      var ranges = new Dictionary<string, List<double>>();
      var positiveBooleans = new HashSet<string>();
      var negativeBooleans = new HashSet<string>();

      foreach (var expr in combination) {
        if (IsInequality(expr, out string? inVarName, out BinaryOperator.Opcode? op, out double? inValue)) {
          if (inVarName == null || op == null || inValue == null) {
            continue;
          }

          if (op == BinaryOperator.Opcode.Eq) {
            if (equalities.TryGetValue(inVarName, out double existingValue)) {
              // E.g.: x == 0 && x == 1
              if (!existingValue.Equals(inValue)) {
                return true;
              } 
            }
            if (inequalities.TryGetValue(inVarName, out double ineqExistingValue)) {
              // E.g.: x == 0 && x != 0
              if (ineqExistingValue.Equals(inValue)) {
                return true;
              } 
            }
            if (ranges.TryGetValue(inVarName, out List<double>? rangeExistingValue)) {
              // E.g.: x >= 0 && x <= 0 && x == 1
              if (rangeExistingValue[1].Equals(rangeExistingValue[2]) &&  !rangeExistingValue[1].Equals(inValue)) {
                return true;
              } 
            }
            equalities[inVarName] = (double)inValue;
            continue;
          }
          
          if (op == BinaryOperator.Opcode.Neq) {
            if (equalities.TryGetValue(inVarName, out double eqExistingValue)) {
              // E.g.: x == 0 && x != 0
              if (eqExistingValue.Equals(inValue)) {
                return true;
              } 
            }
            if (ranges.TryGetValue(inVarName, out List<double>? rangeExistingValue)) {
              // E.g.: x >= 0 && x <= 0 && x != 0
              if (rangeExistingValue[1].Equals(rangeExistingValue[2]) &&  rangeExistingValue[1].Equals(inValue)) {
                return true;
              } 
            }
            inequalities[inVarName] = (double)inValue;
            continue;
          }

          if (double.TryParse(inValue.ToString(), out double doubleValue)) {
            if (!ranges.ContainsKey(inVarName)) {
              // [0] -> include ranges[1] (i.e., ge if 1, gt if 0)
              // [1] -> minimum value
              // [2] -> maximum value
              // [3] -> include ranges[2] (i.e., le if 1, lt if 0)
              ranges[inVarName] = [1, double.NegativeInfinity, double.PositiveInfinity, 1];
            }
          
            var bounds = ranges[inVarName];
            switch (op) {
              case BinaryOperator.Opcode.Gt: 
                bounds[0] = 0;
                bounds[1] = Math.Max(bounds[1], doubleValue);
                break;
              case BinaryOperator.Opcode.Ge:
                bounds[0] = 1;
                bounds[1] = Math.Max(bounds[1], doubleValue);
                break;
              case BinaryOperator.Opcode.Lt: 
                bounds[2] = Math.Min(bounds[2], doubleValue);
                bounds[3] = 0;
                break;
              case BinaryOperator.Opcode.Le:
                bounds[2] = Math.Min(bounds[2], doubleValue);
                bounds[3] = 1;
                break;
            }

            if (bounds[1] > bounds[2]) {
              return true;
            }

            if (bounds[1].Equals(bounds[2])) {
              var eqValue = bounds[1];
              if (bounds[0].Equals(0) || bounds[3].Equals(0)) {
                // E.g.: x > 0 && x <= 0
                return true;
              }
              
              if (inequalities.TryGetValue(inVarName, out double ineqExistingValue)) {
                // E.g.: x >= 0 && x <= 0 && x != 0
                if (eqValue.Equals(ineqExistingValue)) {
                  return true;
                } 
              }
              if (equalities.TryGetValue(inVarName, out double eqExistingValue)) {
                // E.g.: x >= 0 && x <= 0 && x == 5
                if (!eqValue.Equals(eqExistingValue)) {
                  return true;
                } 
              }
              
              equalities[inVarName] = eqValue;
            }
          }
        }

        else if (IsNegated(expr, out string innerName)) {
          if (positiveBooleans.Contains(innerName)) {
            return true;
          }
          
          negativeBooleans.Add(innerName);
        } 
        else if (IsIdentifier(expr, out string posName)) {
          if (negativeBooleans.Contains(posName)) {
            return true;
          }
          positiveBooleans.Add(posName);
        }
      }
      return false;
    }

    /// <summary>
    /// Checks if expr is an Inequality/Equality.
    /// If it is, it returns the variable, the operator, and the value (if it is numeric)
    /// </summary>
    private static bool IsInequality(Expr expr, out string? varName, out BinaryOperator.Opcode? op, out double? value) {
      varName = null; op = null; value = null;
      bool isNegated = false;
      var innerExpr = expr;

      if (expr is NAryExpr { Fun: UnaryOperator { Op: UnaryOperator.Opcode.Not } } naryNot) {
        isNegated = true;
        innerExpr = naryNot.Args[0];
      }

      if (innerExpr is NAryExpr { Fun: BinaryOperator binOp } nary) {
        var a = nary.Args[0];
        var b = nary.Args[1];
        op = GetLogicalOperator(binOp.Op, isNegated);
        if (op == null) {
          return false;
        }

        if (a is IdentifierExpr idExA) {
          varName = idExA.Name;
          if (b is NAryExpr naryB) {
            value = UnpackNAry(naryB);
          }
          else if (b is LiteralExpr litB) {
            var stringVal = litB.Val.ToString();
            if (double.TryParse(stringVal, out double doubleVal)) {
              value = doubleVal;
            }
          }
        }
        else if (b is IdentifierExpr idExB) {
          varName = idExB.Name;
          if (a is NAryExpr naryA) {
            value = UnpackNAry(naryA);
          }
          else if (a is LiteralExpr litA) {
            var stringVal = litA.Val.ToString();
            if (double.TryParse(stringVal, out double doubleVal)) {
              value = doubleVal;
            }
          }
          op = GetLogicalOperator(binOp.Op, isNegated, flipSides: true);
        }
        
        return varName != null && op != null && value != null;
      }
      return false;
    }

    /// <summary>
    /// Unpack NAryExpr and handle possible negations
    /// </summary>
    private static double? UnpackNAry(NAryExpr expr) {
      if (expr.Args[0] is NAryExpr innerExpr) {
        if (expr.Fun is UnaryOperator { Op: UnaryOperator.Opcode.Neg } && innerExpr.Args[0] is LiteralExpr negLit) {
          var stringVal = negLit.Val.ToString();
          if (double.TryParse(stringVal, out double doubleVal)) {
            return doubleVal;
          }
        }
        return UnpackNAry(innerExpr);
      }
      
      else if (expr.Args[0] is LiteralExpr literalExpr) {
        var stringVal = literalExpr.Val.ToString();

        if (expr.Fun is UnaryOperator { Op: UnaryOperator.Opcode.Neg }) {
          if (double.TryParse(stringVal, out double negDoubleVal)) {
            return -negDoubleVal;
          }
        }
        
        if (double.TryParse(stringVal, out double doubleVal)) {
          return doubleVal;
        }
      }
      
      return null;
    }

    /// <summary>
    /// Returns the logical operator if it is ==, !=, gt, lt, ge, le
    /// If isNegated, switch the operator (e.g., gt -> le)
    /// If flipSides, flip the operator (e.g., gt -> lt)
    /// </summary>
    private static BinaryOperator.Opcode? GetLogicalOperator(BinaryOperator.Opcode op, bool isNegated = false, bool flipSides = false) {
      if (op != BinaryOperator.Opcode.Gt && op != BinaryOperator.Opcode.Ge && op != BinaryOperator.Opcode.Lt &&
          op != BinaryOperator.Opcode.Le && op != BinaryOperator.Opcode.Eq &&  op != BinaryOperator.Opcode.Neq) {
        return null;
      }
      var resultOp = op;
      
      if (flipSides) {
        switch (resultOp) {
          case BinaryOperator.Opcode.Gt: resultOp = BinaryOperator.Opcode.Lt; break;
          case BinaryOperator.Opcode.Ge: resultOp = BinaryOperator.Opcode.Le; break;
          case BinaryOperator.Opcode.Lt: resultOp = BinaryOperator.Opcode.Gt; break;
          case BinaryOperator.Opcode.Le: resultOp = BinaryOperator.Opcode.Ge; break;
        }
      }
      
      if (isNegated) {
        switch (resultOp) {
          case BinaryOperator.Opcode.Gt: resultOp = BinaryOperator.Opcode.Le; break;
          case BinaryOperator.Opcode.Ge: resultOp = BinaryOperator.Opcode.Lt; break;
          case BinaryOperator.Opcode.Lt: resultOp = BinaryOperator.Opcode.Ge; break;
          case BinaryOperator.Opcode.Le: resultOp = BinaryOperator.Opcode.Gt; break;
          case BinaryOperator.Opcode.Eq: resultOp = BinaryOperator.Opcode.Neq; break;
          case BinaryOperator.Opcode.Neq: resultOp = BinaryOperator.Opcode.Eq; break;
        }
      }
      return resultOp;
    }
    
    /// <summary>
    /// Checks is an IdentifierExpr is negated.
    /// </summary>
    private static bool IsNegated(Expr expr, out string innerName) {
      innerName = "";
      if (expr is NAryExpr { Fun: UnaryOperator { Op: UnaryOperator.Opcode.Not } } nary) {
        if (nary.Args[0] is IdentifierExpr id) { 
          innerName = id.Name; 
          return true; }
      }
      return false;
    }

    /// <summary>
    /// Checks if expr is IdentifierExpr.
    /// </summary>
    private static bool IsIdentifier(Expr expr, out string name) {
      name = "";
      if (expr is IdentifierExpr id) {
        name = id.Name; 
        return true;
      }
      return false;
    }
  }
}