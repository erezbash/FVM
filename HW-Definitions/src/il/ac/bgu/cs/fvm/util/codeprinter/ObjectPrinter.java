package il.ac.bgu.cs.fvm.util.codeprinter;

import java.io.PrintWriter;

/**
 * Prints the code needed to generate an object.
 * 
 * @param <T> the type of object being printed.
 * 
 */
public interface ObjectPrinter<T> {
   
   void print( T obj, TsPrinter tsp, PrintWriter out ); 
    
}
