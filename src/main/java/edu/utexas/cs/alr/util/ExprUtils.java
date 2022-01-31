package edu.utexas.cs.alr.util;

import edu.utexas.cs.alr.ast.*;
import edu.utexas.cs.alr.parser.ExprBaseListener;
import edu.utexas.cs.alr.parser.ExprLexer;
import edu.utexas.cs.alr.parser.ExprParser;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.ParseCancellationException;
import org.antlr.v4.runtime.tree.ParseTreeWalker;

import java.io.IOException;
import java.io.InputStream;
import java.io.PrintStream;
import java.util.*;

import static edu.utexas.cs.alr.ast.ExprFactory.*;

public class ExprUtils
{
    public static Expr toCNF(Expr expr)
    {
        Expr x = toNNF(expr);
        System.out.println("AFTER NNF TRANSFORM");
        System.out.println(x);

        throw new UnsupportedOperationException("implement this");
    }

    public static Expr toNNF(Expr expr) {

        Expr.ExprKind ek = expr.getKind();
        switch (ek)
        {
            case VAR:
                return expr;
            case NEG:
                // cast for testing and development - maybe push down
                NegExpr nexpr = (NegExpr) expr;

                Expr.ExprKind ek2 = nexpr.getExpr().getKind();
                switch (ek2)
                {
                    case VAR:
                        return expr;
                    case NEG:
                        // NEED TO TEST THIS (DOUBLE NEGATIVE)
                        return nexpr.getExpr();
                    case AND:
                        Expr left = ((AndExpr) nexpr.getExpr()).getLeft();
                        NegExpr negLeft = mkNEG(left);
                        Expr NNFleft = toNNF(negLeft);
                        Expr right = ((AndExpr) nexpr.getExpr()).getRight();
                        NegExpr negRight = mkNEG(right);
                        Expr NNFright = toNNF(negRight);
                        return mkOR(NNFleft, NNFright);
                    case OR:
                        Expr left2 = ((OrExpr) nexpr.getExpr()).getLeft();
                        NegExpr negLeft2 = mkNEG(left2);
                        Expr NNFleft2 = toNNF(negLeft2);
                        Expr right2 = ((OrExpr) nexpr.getExpr()).getRight();
                        NegExpr negRight2 = mkNEG(right2);
                        Expr NNFright2 = toNNF(negRight2);
                        return mkAND(NNFleft2, NNFright2);
                    case IMPL:
                    case EQUIV:
                        //FOR IMPLICATION AND EQUIVALENCE
                        // first do nnf, then apply negative
                        // then do nnf again?
                        Expr e = nexpr.getExpr();
                        e = toNNF(e);
                        NegExpr ne = mkNEG(e);
                        return toNNF(ne);
                }
                break;

            case AND:
                // recurse on left and right sides
                System.out.println(expr.getKind());
                System.out.println(ek);
                Expr left = toNNF(((AndExpr) expr).getLeft());
                Expr right = toNNF(((AndExpr) expr).getRight());
                // return AND of NNF'd left and right sides
                return mkAND(left, right);

            case OR:
                // RECURSE ON LEFT AND RIGHT SIDES, THEN RETURN OR
                Expr leftOr = toNNF(((OrExpr) expr).getLeft());
                Expr rightOr = toNNF(((OrExpr) expr).getRight());
                return mkOR(leftOr, rightOr);
            case IMPL:
                // IN NNF, IMPLICATION p -> q becomes !p or q
                System.out.println(expr);
                Expr ant = ((ImplExpr) expr).getAntecedent();
                System.out.println(ant);
                Expr negAntNNF = toNNF(mkNEG(ant));
                System.out.println(negAntNNF);

                Expr cons = ((ImplExpr) expr).getConsequent();
                System.out.println(cons);
                Expr consNNF = toNNF(cons);

                return mkOR(negAntNNF, consNNF);
            case EQUIV:
                // equiv p iff q becomes (!p or q) and (!q or p)
                Expr Eqleft = ((EquivExpr) expr).getLeft();
                Expr NNFLeft = toNNF(Eqleft);
                Expr negLeftNNF = toNNF(mkNEG(Eqleft));

                Expr Eqright = ((EquivExpr) expr).getRight();
                Expr NNFRight = toNNF(Eqright);
                Expr negRightNNF = toNNF(mkNEG(Eqright));

                Expr newLeft = mkOR(negLeftNNF, NNFRight);
                Expr newRight = mkOR(negRightNNF, NNFLeft);
                return mkAND(newLeft, newRight);

        }

        return expr;
    }

    public static Expr toTseitin(Expr expr)
    {
        throw new UnsupportedOperationException("implement this");
    }

    public static boolean checkSAT(Expr expr)
    {
        throw new UnsupportedOperationException("implement this");
    }

    public static Expr parseFrom(InputStream inStream) throws IOException
    {
        ExprLexer lexer = new ExprLexer(CharStreams.fromStream(inStream));
        BufferedTokenStream tokenStream = new BufferedTokenStream(lexer);
        ExprParser parser = new ExprParser(tokenStream);

        parser.addErrorListener(ThrowingErrorListener.INSTANCE);
        lexer.addErrorListener(ThrowingErrorListener.INSTANCE);

        ExprParser.ExprContext parseTree = parser.expr();
        ASTListener astListener = new ASTListener();
        ParseTreeWalker.DEFAULT.walk(astListener, parseTree);

        return astListener.pendingExpr.pop();
    }

    public static void printDimcas(Expr expr, PrintStream out)
    {
        Set<Set<Long>> clauses = new HashSet<>();
        Set<Long> vars = new HashSet<>();

        Stack<Expr> s = new Stack<>();
        s.push(expr);

        while (!s.isEmpty())
        {
            Expr e = s.pop();

            if (!canBeCNF(e))
                throw new RuntimeException("Expr is not in CNF.");

            switch (e.getKind())
            {
                case AND:
                    AndExpr andExpr = (AndExpr) e;
                    s.push(andExpr.getLeft());
                    s.push(andExpr.getRight());
                    break;
                case NEG:
                    if (!isLiteral(e))
                        throw new RuntimeException("Expr is not in CNF.");

                    VarExpr childVarExpr = (VarExpr) ((NegExpr) e).getExpr();

                    clauses.add(Collections.singleton(-childVarExpr.getId()));
                    vars.add(childVarExpr.getId());
                    break;
                case VAR:
                    VarExpr varExpr = (VarExpr) e;
                    clauses.add(Collections.singleton(varExpr.getId()));
                    vars.add(varExpr.getId());
                    break;
                case OR:
                    clauses.add(getLiteralsForClause((OrExpr) e, vars));
                    break;
                default:
                    assert false;
            }
        }

        out.println("p cnf " + vars.size() + " " + clauses.size());

        clauses.forEach(c -> {
            c.forEach(l -> out.print(l + " "));
            out.println(0);
        });
    }

    public static boolean canBeCNF(Expr e)
    {
        Expr.ExprKind eKind = e.getKind();
        return eKind != Expr.ExprKind.EQUIV &&
               eKind != Expr.ExprKind.IMPL;
    }

    public static boolean isLiteral(Expr e)
    {
        Expr.ExprKind eKind = e.getKind();
        if (eKind == Expr.ExprKind.VAR)
            return true;

        if (eKind == Expr.ExprKind.NEG)
        {
            return ((NegExpr) e).getExpr().getKind() == Expr.ExprKind.VAR;
        }

        return false;
    }

    private static Set<Long> getLiteralsForClause(OrExpr orExpr, Set<Long> vars)
    {
        Set<Long> literals = new HashSet<>();
        Stack<Expr> s = new Stack<>();
        s.add(orExpr.getLeft());
        s.add(orExpr.getRight());

        while (!s.isEmpty())
        {
            Expr e = s.pop();

            if (e.getKind() != Expr.ExprKind.OR && !isLiteral(e))
                throw new RuntimeException("Expr is not in CNF");

            switch (e.getKind())
            {
                case OR:
                    OrExpr or = (OrExpr) e;
                    s.push(or.getLeft());
                    s.push(or.getRight());
                    break;
                case VAR:
                    long varId = ((VarExpr) e).getId();
                    literals.add(varId);
                    vars.add(varId);
                    break;
                case NEG:
                    NegExpr neg = (NegExpr) e;
                    long litId = -((VarExpr)neg.getExpr()).getId();
                    literals.add(litId);
                    vars.add(-litId);
                    break;
                default:
                    assert false;
            }
        }
        return literals;
    }
}

class ASTListener extends ExprBaseListener
{
    Stack<Expr> pendingExpr = new Stack<>();

    @Override
    public void exitAtom(ExprParser.AtomContext ctx)
    {
        long id = Long.parseLong(ctx.VAR().toString().substring(1));
        VarExpr var = mkVAR(id);

        pendingExpr.push(var);
    }

    @Override
    public void exitLneg(ExprParser.LnegContext ctx)
    {
        Expr expr = pendingExpr.pop();
        NegExpr negExpr = mkNEG(expr);

        pendingExpr.push(negExpr);
    }

    @Override
    public void exitLand(ExprParser.LandContext ctx)
    {
        Expr right = pendingExpr.pop(), left = pendingExpr.pop();
        AndExpr andExpr = mkAND(left, right);

        pendingExpr.push(andExpr);
    }

    @Override
    public void exitLor(ExprParser.LorContext ctx)
    {
        Expr right = pendingExpr.pop(), left = pendingExpr.pop();
        OrExpr orExpr = mkOR(left, right);

        pendingExpr.push(orExpr);
    }

    @Override
    public void exitLimpl(ExprParser.LimplContext ctx)
    {
        Expr consequent = pendingExpr.pop(), antecedent = pendingExpr.pop();
        ImplExpr implExpr = mkIMPL(antecedent, consequent);

        pendingExpr.push(implExpr);
    }

    @Override
    public void exitLequiv(ExprParser.LequivContext ctx)
    {
        Expr right = pendingExpr.pop(), left = pendingExpr.pop();
        EquivExpr equivExpr = mkEQUIV(left, right);

        pendingExpr.push(equivExpr);
    }
}

class ThrowingErrorListener extends BaseErrorListener
{

    public static final ThrowingErrorListener INSTANCE = new ThrowingErrorListener();

    @Override
    public void syntaxError(Recognizer<?, ?> recognizer, Object offendingSymbol, int line, int charPositionInLine, String msg, RecognitionException e)
            throws ParseCancellationException
    {
        throw new ParseCancellationException("line " + line + ":" + charPositionInLine + " " + msg);
    }
}
