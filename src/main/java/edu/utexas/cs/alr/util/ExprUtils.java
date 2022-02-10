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

    public static int varCounter = 10000;
    public static Set<Expr> tseitinExprs = new LinkedHashSet<>();
    public static Set<Expr> CNFExprs = new LinkedHashSet<>();
    public static boolean firstExpr = true;

    // for converting
    public static Set<Set<Long>> globalClauses = new LinkedHashSet<>();
    public static Set<Long> globalVars = new LinkedHashSet<>();

    public static ArrayList<Set<Long>> globalWorkingClauses = new ArrayList<>();
    public static ArrayList<Integer> satisfiedClauses = new ArrayList<>();

    // this may need to be altered at some point to allow decision level lists
    // this keeps track of what has been assigned to true - basically unit variables
    public static HashMap<Long, Boolean> assignments = new HashMap<>();

    public static Expr toCNF(Expr expr)
    {
        Expr nnfExp = toNNF(expr);
//        System.out.println("AFTER NNF TRANSFORM");
//        System.out.println(nnfExp);
//        System.out.println("AFTER CNF TRANSFORM");
        Expr test = toCNFHelper(nnfExp);
//        System.out.println(test);
        //return toCNFHelper(nnfExp);

        test = toCNFHelper(test);
        return test;
    }

    // method to perform CNF work;
    // we want second method so that call to toNNF does not get called unnecessarily for each recursive call to toCNF
    public static Expr toCNFHelper(Expr expr){

        switch (expr.getKind()){
            // because we are already in NNF FORM, we know that both
            // var's and neg's are in base form
            // we also know that there are no IMPL or EQUIV
            case VAR:
            case NEG:
                return expr;
            case AND:
                // make sure both sides of and are in CNF form,
                // then return conjunction of them
                Expr left = toCNFHelper(((AndExpr) expr).getLeft());
                Expr right = toCNFHelper(((AndExpr) expr).getRight());
                return mkAND(left, right);
            case OR:
                Expr orLeft = toCNFHelper(((OrExpr) expr).getLeft());
                Expr orRight = toCNFHelper(((OrExpr) expr).getRight());
                // base case where both sides are var's or negs

                Expr.ExprKind leftKind = orLeft.getKind();
                Expr.ExprKind rightKind = orRight.getKind();

                // check whether left hand side of equation is a base case
                boolean leftBase = leftKind.equals(Expr.ExprKind.VAR) || leftKind.equals(Expr.ExprKind.NEG);
                boolean rightBase = rightKind.equals(Expr.ExprKind.VAR) || rightKind.equals(Expr.ExprKind.NEG);
                // both left and right of or are base cases, so can just return this expression
                if(leftBase && rightBase){
                    return expr;
                } else if(leftBase){
                    // distribute left base case over right
                    switch (orRight.getKind()){
                        case OR:
                            return mkOR(orLeft, orRight);
                        case AND:
                            // TODO: this may need to be expanded if necessary for larger clauses
                            // this should work for simple cases
                            // might need to recurse again
                            Expr innerRight = ((AndExpr) orRight).getRight();
                            Expr innerLeft = ((AndExpr) orRight).getLeft();
                            Expr newLeft = toCNFHelper(mkOR(orLeft, innerLeft));
                            Expr newRight = toCNFHelper(mkOR(orLeft, innerRight));
                            return mkAND(newLeft, newRight);
                    }
                } else if (rightBase){
                    switch (orLeft.getKind()){
                        case OR:
                            return mkOR(orLeft, orRight);
                        case AND:
                            // TODO: this may need to be expanded if necessary for larger clauses
                            // this should work for simple cases
                            // might need to recurse again
                            Expr innerRight = ((AndExpr) orLeft).getRight();
                            Expr innerLeft = ((AndExpr) orLeft).getLeft();

                            Expr newLeft = toCNFHelper(mkOR(innerLeft, orRight));
                            Expr newRight = toCNFHelper(mkOR(innerRight, orRight));

                            return mkAND(newLeft, newRight);
                    }
                } else{
                    // both cases are complex
                    Expr leftLeft;
                    Expr leftRight;
                    if(orLeft.getKind().equals(Expr.ExprKind.AND)){
                        leftLeft = ((AndExpr) orLeft).getLeft();
                        leftRight = ((AndExpr) orLeft).getRight();
                    }else{
                        leftLeft = ((OrExpr) orLeft).getLeft();
                        leftRight = ((OrExpr) orLeft).getRight();
                    }

                    Expr rightLeft;
                    Expr rightRight;
                    if(orRight.getKind().equals(Expr.ExprKind.AND)){
                        rightLeft = ((AndExpr) orRight).getLeft();
                        rightRight = ((AndExpr) orRight).getRight();
                    }else{
                        rightLeft = ((OrExpr) orRight).getLeft();
                        rightRight = ((OrExpr) orRight).getRight();
                    }

                    Expr firstOr = toCNFHelper(mkOR(leftLeft, rightLeft));
                    Expr secondOr = toCNFHelper(mkOR(leftLeft, rightRight));
                    Expr thirdOr = toCNFHelper(mkOR(leftRight, rightLeft));
                    Expr forthOr = toCNFHelper(mkOR(leftRight, rightRight));

                    Expr firstAnd = toCNFHelper(mkAND(firstOr, secondOr));
                    Expr secondAnd = toCNFHelper(mkAND(thirdOr, forthOr));
                    return toCNFHelper(mkAND(firstAnd, secondAnd));


                }
        }
        throw new UnsupportedOperationException("YOU SHOULD NEVER REACH THIS\n");
        //return expr;
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
                        return ((NegExpr)nexpr.getExpr()).getExpr();
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
                        // might be able to optimize this if it is a bottleneck
                        Expr e = nexpr.getExpr();
                        e = toNNF(e);
                        NegExpr ne = mkNEG(e);
                        return toNNF(ne);
                }
                break;

            case AND:
                // recurse on left and right sides
//                System.out.println(expr.getKind());
//                System.out.println(ek);
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
                //System.out.println(expr);
                Expr ant = ((ImplExpr) expr).getAntecedent();
                //System.out.println(ant);
                Expr negAntNNF = toNNF(mkNEG(ant));
                //System.out.println(negAntNNF);

                Expr cons = ((ImplExpr) expr).getConsequent();
                //System.out.println(cons);
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
        // convert to tseitin form:
        Expr converted = toTseitinHelper(expr);

        // this means that the expr is either a var
        // or a negative of a var
        // so return just the expression
        if(tseitinExprs.isEmpty()){
            System.out.println("SET IS EMPTY");
            System.out.println(expr);
            return expr;
        }else{
            // loop through the HashSet, get CNF of each element
            // and join in a conjunction

            /*
            int size = tseitinExprs.size();
            Expr[] tseitinArr = tseitinExprs.toArray(new Expr[size]);
            System.out.println(tseitinArr[0]);
            Expr first = toCNF(tseitinArr[0]);

            if(size > 1){
                for(int i = 1; i < size; i++){
                    first = mkAND(first, toCNF(tseitinArr[i]));
                }
            }
            System.out.println(first);
            return first;*/
            // convert tseitin's to cnf:
            for(Expr exp : tseitinExprs) {
                Expr c = toCNF(exp);
                getLongs(c);
                //System.out.println(c);
                //CNFExprs.add(toCNF(exp));
            }

            // COMMENT ALL OF THIS OUT - JUST FOR TESTING
            /*
            for(Set<Long> sl : globalClauses){
                System.out.println("IN NEW OUTER SET: ");
                for (Long l : sl){
                    System.out.println("Long value: " + l);
                }
            }*/
            // LIKELY NEED TO CHANGE RETURN TYPE HERE?
            return expr;
        }
    }

    public static Expr toTseitinHelper(Expr expr){

        switch (expr.getKind()) {
            case VAR:
                return expr;
            case NEG:
                NegExpr nexpr = (NegExpr) expr;

                Expr.ExprKind ek2 = nexpr.getExpr().getKind();
                // base case for negative = !var, so can just return that expression
                if(ek2.equals(Expr.ExprKind.VAR)){
                    return expr;
                }else{
                    VarExpr v1 = mkVAR(varCounter);
                    if(firstExpr){
                        tseitinExprs.add(v1);
                        firstExpr = false;
                    }
                    Expr tmpExpr = mkEQUIV(v1, expr);
                    varCounter++;
                    tseitinExprs.add(tmpExpr);

                    //System.out.println(nexpr.getExpr());
                    Expr inner = toTseitinHelper(nexpr.getExpr());
                    // don't know if returns are really necessary here?
                    return inner;
                }
            case AND:
                VarExpr v2 = mkVAR(varCounter);
                if(firstExpr){
                    tseitinExprs.add(v2);
                    firstExpr = false;
                }
                Expr tmpExpr = mkEQUIV(v2, expr);
                varCounter++;
                tseitinExprs.add(tmpExpr);
                Expr left = toTseitinHelper(((AndExpr)expr).getLeft());
                Expr right = toTseitinHelper(((AndExpr)expr).getRight());
                return expr;
            case OR:
                VarExpr v3 = mkVAR(varCounter);
                if(firstExpr){
                    tseitinExprs.add(v3);
                    firstExpr = false;
                }
                Expr tmpExprOr = mkEQUIV(v3, expr);
                varCounter++;
                tseitinExprs.add(tmpExprOr);
                Expr leftOr = toTseitinHelper(((OrExpr)expr).getLeft());
                Expr rightOr = toTseitinHelper(((OrExpr)expr).getRight());
                return expr;
            case IMPL:
                VarExpr v4 = mkVAR(varCounter);
                if(firstExpr){
                    tseitinExprs.add(v4);
                    firstExpr = false;
                }
                Expr tmpImplExpr = mkEQUIV(v4, expr);
                varCounter++;
                tseitinExprs.add(tmpImplExpr);
                Expr ant = toTseitinHelper(((ImplExpr)expr).getAntecedent());
                Expr cons = toTseitinHelper(((ImplExpr)expr).getConsequent());
                return expr;
            case EQUIV:
                VarExpr v5 = mkVAR(varCounter);
                if(firstExpr){
                    tseitinExprs.add(v5);
                    firstExpr = false;
                }
                Expr tmpEquiveExpr = mkEQUIV(v5, expr);
                varCounter++;
                tseitinExprs.add(tmpEquiveExpr);
                Expr first = toTseitinHelper(((EquivExpr)expr).getLeft());
                Expr second = toTseitinHelper(((EquivExpr)expr).getRight());
                return expr;
        }

        return expr;
    }

    // perform preprocessing on final CNF expression
    // this goes through the clauses and removes clauses that contain
    // a variable in both positive and negative form
    public static void preprocess(){
        //System.out.println("IN PREPROCESS");
        for(Set<Long> sl : globalClauses){
            //System.out.println("IN NEW OUTER SET: ");
            boolean found = false;
            for (Long l : sl){
                for(long k : sl){
                    int test1 = l.compareTo(-k);
                    if(test1 == 0){
                        //System.out.println("TEST PASSED");
                        found = true;
                    }
                }
            }
            if(!found){
                globalWorkingClauses.add(sl);
            }
        }

        System.out.println("PRINTING GLOBAL WORKING CLAUSES");
        for(Set<Long> sl : globalWorkingClauses){
            System.out.println("IN NEW OUTER SET: ");
            for (Long l : sl){
                System.out.println("Long value: " + l);
            }
        }
        System.out.println("LEAVING PREPROCESS");


    }

    // test if an expression (represented as Set<Long>) resolves to a unit expression
    // tests against assignments to see if all variables except one have been resolved to their opposing values
    // this should only be called after a check to see if expr is satisfied already
    // so only works for unsatisfied clauses
    public static boolean checkUnit(Set<Long> expr){
        int testSize = expr.size();
        for(Long l : expr){
            if(assignments.containsKey(-l)){
                testSize--;
            }
        }
        if(testSize > 1){
            return false;
        }else{
            System.out.println("SIZE: " + testSize);
            return true;
        }
    }

    // same as method above, but returns size of number of variables left
    // if its 1, then we have a unit variable
    // if its more than 1, than we can't keep going
    // if its 0, then we have a conflict and an unsat situation
    public static long checkUnitSize(Set<Long> expr){
        int testSize = expr.size();
        for(Long l : expr){
            if(assignments.containsKey(-l)){
                testSize--;
            }
        }
        return testSize;
    }

    // gets the last unassigned variable in a clause - this represents a new unit variable
    public static long getUnitVarFromExpr(Set<Long> expr){
        System.out.println("ENTERING GET VAR");


        if(expr.size() == 1){
            Iterator<Long> itr = expr.iterator();
            Long l = itr.next();
            System.out.println("RETURNING: " + l);
            return l;
        }else{
            // get last unassigned value
            for(Long l : expr){
                // variable does not have opposing mapping in assignments
                // so return it
                System.out.println("L: " + l);
                if(!assignments.containsKey(-l)){
                    System.out.println("RETURNING " + l);
                    return l;
                }
            }
        }

        // this is a dummy value
        // we should never get to it
        return -8675309;
    }

    // Perform exhaustive unit resolution
    // if stop removing elements, will need to change logic here as well
    // boolean test checks to see if BCP resolves to an unSAT
    public static boolean performBCP(){
        int size;
        // use do/while loop to perform exhaustive resolution
        // after each attempt at resolution we will check to see if the size of the
        // resolved clauses list has changed
        // if it has, then more resolution might be possible
        // if not, then resolution is done
        do{
            size = satisfiedClauses.size();
            for(int i = 0; i < globalWorkingClauses.size(); i++){
                // find a unit clause
                // First make sure clause is not already satisfied,
                // then test if size is one or if it resolves to unit
                Set<Long> currentExpr = globalWorkingClauses.get(i);
                //if(!satisfiedClauses.contains(i) && (currentExpr.size() == 1 || checkUnit(currentExpr))){
                Long clauseSize = checkUnitSize(currentExpr);
                // if clauseSize == 0, then we have an unsatisfiable clause after unit resolution
                if(clauseSize == 0) {
                    return false;
                } else if(!satisfiedClauses.contains(i) && (currentExpr.size() == 1 || clauseSize == 1)){

                    // unit variable must be resolved to true - otherwise, would be unsat
                    // we've found clauses that can be resolved
                    // add assignment and mark unit clause as resolved
                    Long var = getUnitVarFromExpr(currentExpr);
                    assignments.put(var, true);
                    satisfiedClauses.add(i);

                    // restart outer loop
                    break;
                }
            }
        } while(!(size == satisfiedClauses.size()));
        return true;
    }

    // check's to see if all clauses have been satisfied
    // use this after running BCP
    // just need to check whether size of satisfied clauses equals size of all clauses
    public static boolean checkAllClauses(){
        System.out.println("satisfied: " + satisfiedClauses.size());
        System.out.println("global working: " + globalWorkingClauses.size());
        return (satisfiedClauses.size() == globalWorkingClauses.size());
    }

    public static boolean checkSAT(Expr expr)
    {
        // check if expr is already in CNF
        // if so, don't need to do Tseitin
        if(!checkCNF(expr)){
            Expr e = toTseitin(expr);
        }else{
            System.out.println("ALREADY IN CNF");
            getLongs(expr);
        }

        preprocess();



        boolean bcpCheck = performBCP();

        for(int i = 0; i < satisfiedClauses.size(); i++){
            System.out.println(satisfiedClauses.get(i));
        }
        System.out.println("PRINTING ASSIGNMENTS");
        for(Long key : assignments.keySet()){
            System.out.println(key);
        }

        if(!bcpCheck){
            return false;
        } else if(checkAllClauses()){
            return true;
        }




        throw new UnsupportedOperationException("implement this");
        //return true;
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

    public static void getLongs(Expr expr){
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

                    globalClauses.add(Collections.singleton(-childVarExpr.getId()));
                    globalVars.add(childVarExpr.getId());
                    break;
                case VAR:
                    VarExpr varExpr = (VarExpr) e;
                    globalClauses.add(Collections.singleton(varExpr.getId()));
                    globalVars.add(varExpr.getId());
                    break;
                case OR:
                    globalClauses.add(getLiteralsForClause((OrExpr) e, globalVars));
                    break;
                default:
                    assert false;
            }
        }
    }

    public static boolean checkCNF(Expr expr)
    {
        Set<Set<Long>> clauses = new HashSet<>();
        Set<Long> vars = new HashSet<>();

        Stack<Expr> s = new Stack<>();
        s.push(expr);

        while (!s.isEmpty())
        {
            Expr e = s.pop();

            if (!canBeCNF(e))
                return false;

            switch (e.getKind())
            {
                case AND:
                    AndExpr andExpr = (AndExpr) e;
                    s.push(andExpr.getLeft());
                    s.push(andExpr.getRight());
                    break;
                case NEG:
                    if (!isLiteral(e))
                        return false;

                    VarExpr childVarExpr = (VarExpr) ((NegExpr) e).getExpr();

                    break;
                case VAR:
                    VarExpr varExpr = (VarExpr) e;
                    break;
                case OR:
                    break;
                default:
                    assert false;
            }
        }

        return true;
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
