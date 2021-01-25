package edu.utexas.cs.alr;

import edu.utexas.cs.alr.ast.Expr;
import edu.utexas.cs.alr.util.ExprUtils;
import org.antlr.v4.runtime.misc.ParseCancellationException;

import java.io.IOException;

public class CNFDriver
{
    public static void main(String[] args)
    {
        try
        {
            Expr e = ExprUtils.parseFrom(System.in);
            Expr cnfExpr = ExprUtils.toCNF(e);
            ExprUtils.printDimcas(cnfExpr, System.out);
        }
        catch (IOException ex)
        {
            System.err.println(ex.getMessage());
            ex.printStackTrace();
            System.exit(1);
        }
        catch (ParseCancellationException ex)
        {
            ex.printStackTrace();
            System.exit(1);
        }
    }
}
