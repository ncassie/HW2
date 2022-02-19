package edu.utexas.cs.alr.util;

import edu.utexas.cs.alr.ast.*;
import edu.utexas.cs.alr.parser.ExprBaseListener;
import edu.utexas.cs.alr.parser.ExprLexer;
import edu.utexas.cs.alr.parser.ExprParser;
import jdk.javadoc.internal.doclets.toolkit.taglets.LiteralTaglet;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.ParseCancellationException;
import org.antlr.v4.runtime.tree.ParseTreeWalker;

import java.io.IOException;
import java.io.InputStream;
import java.io.PrintStream;
import java.util.*;

import static edu.utexas.cs.alr.ast.ExprFactory.*;

class Vertex{

    Long varLabel;
    int decisionLevel;
    int rank;

    // key is clause index
    // value is variable Label at other end
    LinkedHashMap<Integer, Long> outEdges = new LinkedHashMap<>();
    LinkedHashMap<Integer, Long> inEdges = new LinkedHashMap<>();

    Vertex(){
        //System.out.println("THIS IS JUST FOR TESTING");
        // this is used for conflict node since don't need a decision level or label
    }
    Vertex(Long varLabel, int decisionLevel, int rank){
        this.varLabel = varLabel;
        this.decisionLevel = decisionLevel;
        this.rank = rank;
    }

    Vertex(Long varLabel, int decisionLevel, Integer clauseIndex, Long parentIndex){
        this.varLabel = varLabel;
        this.decisionLevel = decisionLevel;

        inEdges.put(clauseIndex, parentIndex);
    }

    public void addOutEdge(Integer clauseIndex, Long childIndex){
        outEdges.put(clauseIndex, childIndex);
    }

    public void addInEdge(Integer clauseIndex, Long parentIndex){
        inEdges.put(clauseIndex, parentIndex);
    }

    public void clear(){
        this.inEdges.clear();
        this.outEdges.clear();

    }


    public void sayHi(){
        System.out.println("HI");
    }
}

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

    public static LinkedHashMap<Integer, ArrayList<Integer>> satisfiedClausesByLevel = new LinkedHashMap<>();

    // key is Long representing a variable
    // object is ArrayList of indices into globalWorkingClauses in which a variable is a watch literal
    public static HashMap<Long, ArrayList<Integer>> watchLiterals = new HashMap<>();
    // opposite mapping from clause index to watch literals for that clause
    public static HashMap<Integer, ArrayList<Long>> clauseWatchLiterals = new HashMap<>();

    // this may need to be altered at some point to allow decision level lists
    // this keeps track of what has been assigned to true - basically unit variables
    public static HashMap<Long, Boolean> assignments = new HashMap<>();
    public static HashMap<Integer, LinkedHashSet<Long>> assignmentsByLevel = new HashMap<>();

    public static int decisionLevel = 1;
    // decision level/rank
    public static Hashtable<Integer, Integer> rank = new Hashtable<>();
    //public static HashMap<Integer, ArrayList<Long>> unitVars = new HashMap<>();
    // try a stack for now and see if its an issue
    public static HashMap<Integer, Stack<Long>> unitVars = new HashMap<>();

    // Long = parameter assignment
    // Vertex = node in graph
    // use hashmap for easy access to each element
    public static LinkedHashMap<Long, Vertex> implicationGraph = new LinkedHashMap<>();

    // global conflict node so functions can easily access it
    public static Vertex conflictNode = new Vertex();

    public static Long jennyNumber = Long.valueOf(8675309);


    public static Expr toCNF(Expr expr)
    {
        //System.out.println("TO CNF BEING CALLED");
        Expr testExpr;
        Expr nnfExp = toNNF(expr);
        do{
        //    System.out.println("IN OUTER LOOP");
            testExpr = nnfExp;
            nnfExp = toNNF(nnfExp);
        } while(testExpr != nnfExp);


        /*System.out.println("AFTER NNF TRANSFORM");
        System.out.println(nnfExp);
        System.out.println("AFTER CNF TRANSFORM");
*/
        Expr test = toCNFHelper(nnfExp);
  //      System.out.println(test);
        //return toCNFHelper(nnfExp);

        test = toCNFHelper(test);
        return test;
    }

    // method to perform CNF work;
    // we want second method so that call to toNNF does not get called unnecessarily for each recursive call to toCNF
    public static Expr toCNFHelper(Expr expr){
        //System.out.println("CNF HELPER BEING CALLED");
        //System.out.println(expr.getKind());

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
        //System.out.println("NNF CALLED FOR EXP: " + expr);
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

                Expr newLeft = toNNF(mkOR(negLeftNNF, NNFRight));
                Expr newRight = toNNF(mkOR(negRightNNF, NNFLeft));
                return mkAND(newLeft, newRight);
        }

        return expr;
    }

    public static Expr toTseitin(Expr expr)
    {
        // convert to tseitin form:
        Expr converted = toTseitinHelper(expr);
        tseitinExprs.add(converted);

        // this means that the expr is either a var
        // or a negative of a var
        // so return just the expression
        if(tseitinExprs.isEmpty()){
            //System.out.println("SET IS EMPTY");
            //System.out.println(expr);
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
                Expr tmp;
                Expr c = toCNF(exp);
                do{
                    tmp = c;
                    c = toCNF(c);
                }while(tmp != c);



                //System.out.println(c);
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

    // goals here:
    // create new <--> expression and add to global list
    // return new variable created so outer recursion steps can use that version
    // will eventually return top level variable, so toTseitin can add this to list, then prcess everything
    // this functions just creates the <-> expressions. toTseitin will loop through them and CNF them.
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
                    varCounter++;
                    // might be able to eliminate these with proper planning
                    /*if(firstExpr){
                        tseitinExprs.add(v1);
                        firstExpr = false;
                    }*/
                    // call tseitsinHelper on inner expression
                    Expr innerT = toTseitinHelper(nexpr.getExpr());

                    Expr tmpExpr = mkEQUIV(v1, innerT);
                    tseitinExprs.add(tmpExpr);

                    //System.out.println(nexpr.getExpr());
                    //Expr inner = toTseitinHelper(nexpr.getExpr());

                    return v1;
                }
            case AND:
                VarExpr v2 = mkVAR(varCounter);
                varCounter++;
                /*if(firstExpr){
                    tseitinExprs.add(v2);
                    firstExpr = false;
                }*/
                Expr left = toTseitinHelper(((AndExpr)expr).getLeft());
                Expr right = toTseitinHelper(((AndExpr)expr).getRight());
                Expr newAnd = mkAND(left, right);
                Expr tmpExpr = mkEQUIV(v2, newAnd);

                tseitinExprs.add(tmpExpr);

                return v2;
            case OR:
                VarExpr v3 = mkVAR(varCounter);
                varCounter++;
                /*
                if(firstExpr){
                    tseitinExprs.add(v3);
                    firstExpr = false;
                }*/
                Expr leftOr = toTseitinHelper(((OrExpr)expr).getLeft());
                Expr rightOr = toTseitinHelper(((OrExpr)expr).getRight());
                Expr newOr = mkOR(leftOr, rightOr);
                Expr tmpExprOr = mkEQUIV(v3, newOr);
                tseitinExprs.add(tmpExprOr);

                return v3;
            case IMPL:
                VarExpr v4 = mkVAR(varCounter);
                varCounter++;
                /*
                if(firstExpr){
                    tseitinExprs.add(v4);
                    firstExpr = false;
                }*/

                Expr ant = toTseitinHelper(((ImplExpr)expr).getAntecedent());
                Expr cons = toTseitinHelper(((ImplExpr)expr).getConsequent());
                Expr newImpl = mkIMPL(ant, cons);

                Expr tmpImplExpr = mkEQUIV(v4, newImpl);
                tseitinExprs.add(tmpImplExpr);

                return v4;
            case EQUIV:
                VarExpr v5 = mkVAR(varCounter);
                varCounter++;
                /*
                if(firstExpr){
                    tseitinExprs.add(v5);
                    firstExpr = false;
                }*/
                Expr first = toTseitinHelper(((EquivExpr)expr).getLeft());
                Expr second = toTseitinHelper(((EquivExpr)expr).getRight());
                Expr newEquiv = mkEQUIV(first, second);
                Expr tmpEquiveExpr = mkEQUIV(v5, newEquiv);

                tseitinExprs.add(tmpEquiveExpr);

                return v5;
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

        /*
        System.out.println("PRINTING GLOBAL WORKING CLAUSES");
        for(Set<Long> sl : globalWorkingClauses){
            System.out.println("IN NEW OUTER SET: ");
            for (Long l : sl){
                System.out.println("Long value: " + l);
            }
        }
        System.out.println("LEAVING PREPROCESS");*/


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
        //System.out.println("ENTERING GET VAR");


        if(expr.size() == 1){
            Iterator<Long> itr = expr.iterator();
            Long l = itr.next();
          //  System.out.println("RETURNING: " + l);
            return l;
        }else{
            // get last unassigned value
            for(Long l : expr){
                // variable does not have opposing mapping in assignments
                // so return it
                //System.out.println("L: " + l);
                if(!assignments.containsKey(-l)){
            //        System.out.println("RETURNING " + l);
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
    // THIS METHOD IS BASIC/STANDARD BCP - so it is no longer used
    //  new methods were created to incorporate watch literals
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

    // initial attempt at incorporating bcp with watch literals
    // moved to a different function below
    /*
    public static boolean performWatchBCP(){
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

                // current clause is satisfied so don't do any work
                if(!satisfiedClauses.contains(i)){
                    Long clauseSize = checkUnitSize(currentExpr);
                    // if clauseSize == 0, then we have an unsatisfiable clause after unit resolution

                    if(clauseSize == 0) {
                        return false;
                    } else if(currentExpr.size() == 1 || clauseSize == 1){

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

            }
        } while(!(size == satisfiedClauses.size()));
        return true;
    }

     */

    // set initial watch variables for start of analysis
    public static void initWatchLiterals(){
        // loop through list of clauses
        // initialize naively at first- just get first two variables returned from iterator
        // check if hashmap contains a list for each variable
        // if yes, add index to list for that variable
        // if not, create arraylist and add index into globalworkingclauses representing clause number
        // then add hashmap listing from variable to this arraylist

        for(int i = 0; i < globalWorkingClauses.size(); i++){

            Set<Long> clause = globalWorkingClauses.get(i);
            Iterator<Long> itr = clause.iterator();
            // unit clause - so push to stack of unit clauses to analyze
            if(clause.size() == 1){
                Long unit = itr.next();
                unitVars.get(decisionLevel).push(unit);
                // this is only being run at start of analysis, not every run through
                // because we know these clauses are unit length, we can add them as an assignment
                // and mark these clauses as satisfied
                // if later clauses conflict, then we will get an unsat because these need
                // to be assigned as is because it is only length one
                // B/C only doing once, can create new lists and hashtable entries
                // following two lines are from BPC, updated for new approach using watch literals and new data structures
                //assignments.put(unit, true);
                //satisfiedClauses.add(i);
                LinkedHashSet<Long> assigns = assignmentsByLevel.get(decisionLevel);
                assigns.add(unit);
                assignmentsByLevel.put(decisionLevel, assigns);
                ArrayList<Integer> satClauses = satisfiedClausesByLevel.get(decisionLevel);
                satClauses.add(i);
                satisfiedClausesByLevel.put(decisionLevel, satClauses);

                // add new vertex to implication graph for unit variables
                implicationGraph.put(unit, new Vertex(unit, decisionLevel, rank.get(decisionLevel)));
                rank.put(decisionLevel, rank.get(decisionLevel) + 1);
            }
            // size is >1 meaning we need to create watch literals
            if(clause.size() > 1){
                // create new array list for clause->watch literal mapping
                ArrayList<Long> clauseWatchLs = new ArrayList<>();
                for(int j = 0; j < 2; j++){
                    Long var = itr.next();
                    // add clause to list of clauses that variable is watch literal for
                    if(watchLiterals.containsKey(var)){
                        watchLiterals.get(var).add(i);
                    }else{
                        ArrayList<Integer> tmp = new ArrayList<>();
                        tmp.add(i);
                        watchLiterals.put(var, tmp);
                    }

                    // add watch literal to list for this clause
                    clauseWatchLs.add(var);
                }
                clauseWatchLiterals.put(i, clauseWatchLs);
            }
        }
    }

    // this will check the clauses to see if we need to look for new implications
    // based on watch literals
    // parameter is newly assigned variable
    public static boolean checkWatchLiterals(Long assignedVar){
        // make sure -assignedVar is actually a watch literal
        if(watchLiterals.containsKey(-assignedVar)){
            //System.out.println("IN HERE with assgined var " + assignedVar);
            // get list of clauses that variable is watch literal for
            ArrayList<Integer> watchList = watchLiterals.get(-assignedVar);
            //System.out.println(watchList.size());
            // loop over clauses that variable is watch literal for
            for(int i = 0; i < watchList.size(); i++){
                // get clause index from watch list
                int index = watchList.get(i);
                //System.out.println(index);
                //make sure clause is not already satisfied by prior assignment to true
                if(!(satisfiedClausesByLevel.get(decisionLevel).contains(index))){
                    //System.out.println("HERE AGAIN");
                    // get clause and its iterator
                    Set<Long> clause = globalWorkingClauses.get(index);
                    Iterator<Long> itr = clause.iterator();

                    // get watch literal list for this clause
                    ArrayList<Long> clauseWL= clauseWatchLiterals.get(index);

                    // track whether a new watch literal was found
                    // used to see if we can make assignment of other watch literal
                    boolean foundNewWatchVariable = false;

                    // iterate through variables in clause to see if we can assign a new watch variable
                    while(itr.hasNext()){
                        Long currentVar = itr.next();
                        //System.out.println("CURRENT VARIABLE " + currentVar);
                        // check if there is an unassigned variable that is not a watch variable
                        // need to skip over watch variable we are analyzing
                        if(!currentVar.equals(-assignedVar)) {
                            if(!clauseWL.contains(currentVar) && !assignmentsByLevel.get(decisionLevel).contains(currentVar)){
                            //if (!clauseWL.contains(currentVar) && !assignments.containsKey(currentVar)) {
                                // found a new variable to make a watch clause
                                // update clause watch list
                                clauseWL.remove(-assignedVar);
                                clauseWL.add(currentVar);
                                clauseWatchLiterals.put(index, clauseWL);

                                // update watch list for new watch list variable
                                if (watchLiterals.containsKey(currentVar)) {
                                    watchLiterals.get(currentVar).add(index);
                                } else {
                                    ArrayList<Integer> tmp = new ArrayList<>();
                                    tmp.add(index);
                                    watchLiterals.put(currentVar, tmp);
                                }

                                // set flag that we found new variable
                                //System.out.println("WE ARE ABOUT TO RETURN TRUE");
                                foundNewWatchVariable = true;

                                // don't need to check any more variables for this clause because we found a new watch variable
                                break;
                            }
                        }
                    }
                    // no new watch variable was found, so analyze existing watch variable
                    if(!foundNewWatchVariable){
                        clauseWL.remove(-assignedVar);
                        // testing on variable 1 because it wasd giving me issues
                        /*
                        if(assignedVar.equals(Long.valueOf(1))){
                            System.out.println("IMPLYING NE");
                        }*/
                        // If we don't have a second watch variable, something went wrong
                        if(clauseWL.isEmpty()){
                            return false;
                        } else{
                            Long lastWatchLiteral = clauseWL.get(0);
                            //System.out.println("Last watch literal for clause:" + lastWatchLiteral);

                            // check if variable is already assigned
                            // if so, this is fine b/c could be assigned but not processed yet
                            if(assignmentsByLevel.get(decisionLevel).contains(lastWatchLiteral)){
                                // todo - decide if need to check if added as a unit var
                                // TODO - DOUBLE CHECK THAT THESE SHOULD BE -assignedVar here
                                // test should be true, but do it so we don't throw an exception if it doesn't
                                // incoming edge to child/ new implied variable
                                if(implicationGraph.containsKey(lastWatchLiteral)){
                                    //implicationGraph.get(lastWatchLiteral).addInEdge(index, -assignedVar);
                                    // actual assignment caused this implication, so needs to be assignedVar, not -assignedVar
                                    implicationGraph.get(lastWatchLiteral).addInEdge(index, assignedVar);
                                }
                                // outgoing edge from -watchVariable
                                // same note as above - needs to be assignedVar, not -assignedVar because assigneVar
                                // was the assignment that caused this implication
                                if(implicationGraph.containsKey(assignedVar)){
                                    implicationGraph.get(assignedVar).addOutEdge(index, lastWatchLiteral);
                                }
                                // Don't want to return true here because it will stop processing other clauses
                                // that use this as a watch literal - only want to return true in this function at very end
                                //return true;
                            } else if(assignmentsByLevel.get(decisionLevel).contains(-lastWatchLiteral)){
                                // this is a conflict so return false
                                // add edge with this clause into conflict node - this clause is conflicting
                                // TODO - MIGHT NEED TO ADD ADDITIONAL EDGES INTO CONFLICT NODE
                                // TODO - NOT SURE, BECAUSE WE WILL PROCESS ENTIRE CLAUSE THAT LED HERE
                                conflictNode.clear();
                                conflictNode.addInEdge(index, lastWatchLiteral);

                                //System.out.println("RETURNING A CONFLICT");

                                /*Vertex v = implicationGraph.get(-lastWatchLiteral);
                                Integer conflictEdge = v.inEdges.entrySet().iterator().next().getKey();
                                conflictNode.addInEdge(conflictEdge, -lastWatchLiteral); */
                                // we found a conflict, so don't need to process any more clauses containing -var as a watch literal
                                // because we need to adjust assignments to satisfy this conflict
                                return false;
                            } else{
                                // THIS IS A NEW IMPLIED ASSIGNMENT
                                assignmentsByLevel.get(decisionLevel).add(lastWatchLiteral);
                                // make sure this is all correct
                                satisfiedClausesByLevel.get(decisionLevel).add(index);
                                unitVars.get(decisionLevel).push(lastWatchLiteral);
                                Vertex v = new Vertex(lastWatchLiteral, decisionLevel, rank.get(decisionLevel));
                                rank.put(decisionLevel, rank.get(decisionLevel) + 1);
                                // IN EDGE SHOULD BE ASSIGNED VAR, NOT -ASSIGNEDVAR BECAUSE ASSIGNMENT CAUSED IMPLICATION
                                v.addInEdge(index, assignedVar);
                                implicationGraph.put(lastWatchLiteral, v);
                                if(implicationGraph.containsKey(assignedVar)){
                                    implicationGraph.get(assignedVar).addOutEdge(index, lastWatchLiteral);
                                }
                                //return true;
                            }
                        }
                    }
                }
            }
        }
        // got through everything ok, so return true
        return true;
    }

    // check's to see if all clauses have been satisfied
    // use this after running BCP
    // just need to check whether size of satisfied clauses equals size of all clauses
    public static boolean checkAllClauses(){
        //System.out.println("satisfied: " + satisfiedClausesByLevel.get(decisionLevel).size());
        //System.out.println("global working: " + globalWorkingClauses.size());
        return satisfiedClausesByLevel.get(decisionLevel).size() == globalWorkingClauses.size();
        //return (satisfiedClauses.size() == globalWorkingClauses.size());
    }

    public static Long getNewAssignment(){
        for(Long l : globalVars){
            // if variable and its negation are both not assigned, then can use as assignment

            if(!assignmentsByLevel.get(decisionLevel).contains(l) && !assignmentsByLevel.get(decisionLevel).contains(-l)){
                return l;
            }
        }

        // if we return this, then we have no new assignments to make
        return jennyNumber;
    }

    // copies previous level up to new decision level
    // this lets us add to new decision level
    // then revert back to older decision levels easily
    public static void increaseLevel(){
        int tmpLevel = decisionLevel + 1;
        LinkedHashSet<Long> tmpABL = new LinkedHashSet<>();
        tmpABL.addAll(assignmentsByLevel.get(decisionLevel));
        assignmentsByLevel.put(tmpLevel, tmpABL);

        Stack<Long> tmpStack = new Stack<>();
        tmpStack.addAll(unitVars.get(decisionLevel));
        unitVars.put(tmpLevel, tmpStack);

        ArrayList<Integer> tmpSatisfied = new ArrayList<>();
        tmpSatisfied.addAll(satisfiedClausesByLevel.get(decisionLevel));
        satisfiedClausesByLevel.put(tmpLevel, tmpSatisfied);
    }

    // helper method to revert back to earlier level
    // removes all decisions made between new, lower level and current level
    public static void revertToLowerLevel(Integer newLevel){
        for(int i = newLevel + 1; i <= decisionLevel; i++){
            assignmentsByLevel.remove(i);
            unitVars.remove(i);
            satisfiedClausesByLevel.remove(i);
        }
        decisionLevel = newLevel;
    }

    // method to find UIP based on conflict clause
    public static Long findUIP(){
        // get actual conflict clause
        Integer conflictIndex = conflictNode.inEdges.entrySet().iterator().next().getKey();
        Set<Long> clause = globalWorkingClauses.get(conflictIndex);

        /*for(Long l : clause){
            System.out.println(l);
        }*/

        // find variables in last clause assigned at current decision level
        ArrayList<Long> lastVars = new ArrayList<>();

        /*System.out.println("Implication graph size " + implicationGraph.size());
        Set<Long> ks = implicationGraph.keySet();
        for(Long ky : ks){
            System.out.println(ky);
        }*/
        for(Long var : clause){
            //System.out.println("Decision level, var " + decisionLevel + " " + var);
            // updated conflict node instead of creating node for variable, so need to check for this
            if(implicationGraph.containsKey(-var)){
                //System.out.println("Var was in graph " + var);
                if(implicationGraph.get(-var).decisionLevel == decisionLevel){
                    lastVars.add(-var);
                }
            }
        }

        /* if(lastVars.size() == 1){
            //figure out what to do here
            System.out.println("OK, NEED TO FIGURE THIS OUT");
            return jennyNumber;
        }else{ */
            do{
                // remove highest rank variable
                // replace with all parents if they have same decision level
                int testRank = -1;
                Long lastVar = jennyNumber;

                // find variable with highest rank
                for(int i = 0; i < lastVars.size(); i++) {
                    System.out.println(lastVars.get(i));
                    Vertex v = implicationGraph.get(lastVars.get(i));
                    if (v.rank > testRank){
                        testRank = v.rank;
                        lastVar = lastVars.get(i);
                    }
                }

                // loop through parents and add all parents with same decision level
                Vertex v = implicationGraph.get(lastVar);
                //System.out.println(v.decisionLevel);
                Set<Integer> keys = v.inEdges.keySet();
                // keys are clauses labeling incoming edge
                // values associated with key is variable on other end if I need it
                for(Integer key : keys){
                    //System.out.println(key);
                    Long p = v.inEdges.get(key);
                    Vertex parent = implicationGraph.get(p);
                    if(parent.decisionLevel == decisionLevel){
                        lastVars.add(p);
                    }
                }
                if(lastVars.size() > 1){
                    lastVars.remove(lastVar);
                }

            }while(lastVars.size() > 1);
        // }
        return lastVars.get(0);
    }

    // funtion to test whether negation of UIP is only literal at current decision level
    // in a new conflict clause
    public static boolean testUIPCondition(Long negUIP, Set<Long> conflictClause){
        // if negation of UIP isn't in conflict clause yet, test fails
        if(!conflictClause.contains(negUIP)){
            return false;
        }else{
            // loop through variables and if variable other than negUIP is at current decision level,
            // test fails
            for(Long var : conflictClause){
                // don't need to consider negUIP
                if(!var.equals(negUIP)){
                    if(implicationGraph.get(var).decisionLevel == decisionLevel){
                        return false;
                    }
                }
            }
        }
        // two tests passed, so return true
        return true;
    }

    public static Set<Long> resolveTwoClauses(Set<Long> c1, Set<Long> c2){
        //Set<Long> newSet = new LinkedHashSet<>();
        // can use c1 because we are passing a clean set so don't need to worry about altering c1
        //newSet.addAll(c1);
        for(Long var : c2){
            // each clause contains an opposing literal - so resolve by removing
            if(c1.contains(-var)){
                c1.remove(-var);
            }else{
                // otherwise add to set
                // because its a set, if variable is added a second time, it won't be duplicated
                c1.add(var);
            }
        }
        return c1;
    }

    // method to analyze conflict based on UIP
    // find a new conflict clause once we know we have a conflict and adds to list of clauses
    // returns new decision level to backtrack to
    public static Integer analyzeConflict(Long UIP){
        Long negatedUIP = -UIP;
        System.out.println("UIP: " + UIP);
        // get conflict clause index
        Integer conflictIndex = conflictNode.inEdges.entrySet().iterator().next().getKey();
        Set<Long> clause = globalWorkingClauses.get(conflictIndex);

        // find variables in last clause assigned at current decision level
        ArrayList<Long> lastVars = new ArrayList<>();

        for(Long var : clause){
            if(implicationGraph.containsKey(-var)){
                if(implicationGraph.get(-var).decisionLevel == decisionLevel){
                    lastVars.add(-var);
                }
            }

        }
        // NEED TO DEAL WITH THIS ON THE OTHER END!
        //System.out.println("LAST VARS SIZE " + lastVars.size());
        if(lastVars.size() == 1 && lastVars.get(0).equals(UIP)){
            Set<Long> tmp = new LinkedHashSet<>();
            tmp.add(-UIP);
            return -10;
        }
        Set<Long> testSet = new LinkedHashSet<>();
        testSet.addAll(clause);
        boolean testFlag = false;
        while(true){
            // this loops over all edges coming into conflict clause initially
            // will add successive ancestors to it if we don't resolve uip condition
            //System.out.println("STUCK IN CONFLICT ANALYSIS LOOP");
            for(Long var : lastVars){
               // System.out.println(var);
                Vertex v = implicationGraph.get(var);
                Set<Integer> keys = v.inEdges.keySet();

                // keys are clauses labeling incoming edge
                // values associated with key is variable on other end if I need it
                for(Integer key : keys){
                    Set<Long> c2 = globalWorkingClauses.get(key);
                    testSet = resolveTwoClauses(testSet, c2);
                    if(testUIPCondition(negatedUIP, testSet)){
                        testFlag = true;
                        break;
                    }else{
                        // didn't satisfy our condition, so add parent for processing?
                        lastVars.add(v.inEdges.get(key));
                    }
                }
                if(testFlag){
                    break;
                }
            }
            if(testFlag){
                break;
            }
        }
        // add new conflict clause to our global set of clauses
        globalWorkingClauses.add(testSet);

        if(testSet.size() == 1){
            return 1;
        } else{
            int firstMax = -1;
            int secondMax = -1;
            for(Long var : testSet){
                int dl = implicationGraph.get(var).decisionLevel;
                if (dl > firstMax){
                    secondMax = firstMax;
                    firstMax = dl;
                } else if (dl > secondMax){
                    secondMax = dl;
                }
            }
            return secondMax;
        }
    }

    public static boolean checkSATHelper(){
        /* CDCL process:
            First DPLL
                1. Run BCP
                    1a. CDCL - extends this to use watch literals
                    1b. CDCL - extends using implication graph to analyze conflict
                2. Run PLP (If only positive then set to true, if only negative, set to false)
                3. if(PLP) returns TRUE/SAT, then return SAT
                4. if (PLP) return false/unsat then return unsat
                5. choose variable at random
                6. if dpll on variable is true, return sat
                7. else, return dpll of variable set to false
         */

        // run BCP using watch literals
        // need to figure out how to do this exhaustively - doing it for every variable in
        // our unit list, so this should be exhaustive as new variables get added to list as we go through process
        // USE INFINITE LOOP TO CONTINUE PROCESS FOR NOW
        // CAN ADJUST IF PROPER BREAK CONDITIONS LEAD TO GOOD TEST STATEMENT
        while(true){
            // check all of our current unit vars to see if any more assignments can be made
            // this is basically the bcp process
            while(!unitVars.get(decisionLevel).isEmpty()){
                //System.out.println("STUCK IN INNER LOOP decisionLevel + stack size "  + decisionLevel + " " +  unitVars.get(decisionLevel).size());
                Long var = unitVars.get(decisionLevel).pop();
                //System.out.println("VAR ANALYZE: " + var);
                //System.out.println(var);
                boolean check = checkWatchLiterals(var);
                //System.out.println(check);
                // checkWatchLiterals returned false so we know we have a conflict
                if(!check){
                    //System.out.println("ARE WE HAVING FAILING CHECK");
                    // if conflict is at decision level 1, then we know equation is unsat
                    if(decisionLevel == 1){
                        return false;
                    } else{
                        // we have a conflict at a level higher than our first level
                        // so find the first UIP
                        // then analyze conflict to find new conflict clause and get new decision level
                        // revert trackers to back-tracked decision level
                        // then make new assignment/ begin processing based on new assignment from backtracking
                        Long uip = findUIP();
                        int newDecisionLevel = analyzeConflict(uip);
                        // this means our current assignment was bad
                        if(newDecisionLevel == -10){

                        }
                        revertToLowerLevel(newDecisionLevel);

                        // new conflict clause is last item in globalClauses
                        Set<Long> conflictClause = globalWorkingClauses.get(globalWorkingClauses.size()-1);
                        unitVars.get(decisionLevel).push(getUnitVarFromExpr(conflictClause));

                    }
                }
                // no conflict, so proceed to the next unitVar in our list and process that
            }
            if(checkAllClauses()){
                //System.out.println("Returning true after check all clauses");
                return true;
            }else{
                // Process has exhausted implied assignments, so increase decision level and make new assignment
                increaseLevel();
                decisionLevel++;
                rank.put(decisionLevel, 0);
                Long varAssign = getNewAssignment();
                if(varAssign == jennyNumber){
                    // can't make new assignment and haven't satisfied all clauses, so check level?
                    //System.out.println("867 was a var assign");
                    return true;
                }else{
                    assignmentsByLevel.get(decisionLevel).add(varAssign);
                }
                implicationGraph.put(varAssign, new Vertex(varAssign, decisionLevel, rank.get(decisionLevel)));
                rank.put(decisionLevel, rank.get(decisionLevel) + 1);
                //System.out.println("VARIABLE ASSIGNMENT " + varAssign);
                // push new assignment for analysis in next round of loop
                // NOTE - unitVars is a bad name for this variable
                unitVars.get(decisionLevel).push(varAssign);
                // TODO - NEED TO MARK ALL CLAUSES CONTAINING THIS VARIABLE AS SATISFIED!
                // TODO - FIND A BETTER WAY TO DO THIS - PROBABLY NEED A HASHTABLE OF VAR->CLAUSES THAT WE CAN ACCESS
                for(int k = 0; k < globalWorkingClauses.size(); k++){
                    if(globalWorkingClauses.get(k).contains(varAssign)){
                        satisfiedClausesByLevel.get(decisionLevel).add(k);
                    }
                }
            }
        }

        //return true;
    }

    // use a helper function so that toTseitin processing doesn't continually happen if recursion is used
    public static boolean checkSAT(Expr expr)
    {
        Stack<Long> firstLevelUnits = new Stack<>();
        unitVars.put(decisionLevel, firstLevelUnits);
        LinkedHashSet<Long> firstAssigns = new LinkedHashSet<>();
        assignmentsByLevel.put(decisionLevel, firstAssigns);
        ArrayList<Integer> firstSat = new ArrayList<>();
        satisfiedClausesByLevel.put(decisionLevel, firstSat);
        rank.put(decisionLevel, 0);

        // check if expr is already in CNF
        // if so, don't need to do Tseitin
/*
        if(!checkCNF(expr)){
            System.out.println("Line 1233 : TOSEITIN being called");
            Expr e = toTseitin(expr);
        }else{
            System.out.println("ALREADY IN CNF");
            getLongs(expr);
        }*/

        Expr e = toTseitin(expr);
        //getLongs(expr);

        //System.out.println("FINISHED TOSEITIN");

        // preprocess removes all clauses that contain a variable and its negation
        preprocess();

        //System.out.println(globalWorkingClauses.size());

        initWatchLiterals();

        //System.out.println("ABOUT TO START THE REAL WORK");

        // key is Long representing a variable
        // object is ArrayList of indices into globalWorkingClauses in which a variable is a watch literal


        //public static HashMap<Integer, ArrayList<Long>> clauseWatchLiterals = new HashMap<>();
        /*Set<Integer> keys = clauseWatchLiterals.keySet();
        for(Integer key : keys){
            System.out.println("Cluase index: " + key);
            ArrayList<Long> tmp = clauseWatchLiterals.get(key);
            for(int i = 0; i < tmp.size(); i++){
                System.out.println(tmp.get(i));
            }
        }*/

        // break this into two statements in case we want to do testing after checkSATHELPER runs
        boolean satTest = checkSATHelper();

        return satTest;

        //boolean bcpCheck = performBCP();
        /* BELOW IS ALL JUST FOR TESTING
        Vertex n = new Vertex();
        n.sayHi();

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
        }*/

        // throw new UnsupportedOperationException("implement this");
        //return true;
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
                    //System.out.println(e);
                    globalClauses.add(getLiteralsForClause((OrExpr) e, globalVars));
                    break;
                default:
                    assert false;
            }
        }
    }

    // checks to see if expression is already in CNF form
    // if so, then we don't need to do Tseitsin encoding on it
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
