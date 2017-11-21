package il.ac.bgu.cs.fvm.nanopromela;

import java.io.IOException;

import org.antlr.v4.runtime.ANTLRFileStream;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.ParserRuleContext;

import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaParser.StmtContext;
import java.io.InputStream;

public class NanoPromelaFileReader {
    
    public static StmtContext parseNanoPromelaStream( InputStream in ) throws IOException {
        NanoPromelaLexer lexer = new NanoPromelaLexer(new ANTLRInputStream(in) );
		CommonTokenStream tokens = new CommonTokenStream(lexer);
		NanoPromelaParser parser = new NanoPromelaParser(tokens);
		ParserRuleContext tree = parser.stmt();

		StmtContext root = (StmtContext) tree.getRuleContext();
		return root;
    }
    
	public static StmtContext pareseNanoPromelaFile(String filename) throws IOException {
		NanoPromelaLexer lexer = new NanoPromelaLexer(new ANTLRFileStream(filename));
		CommonTokenStream tokens = new CommonTokenStream(lexer);
		NanoPromelaParser parser = new NanoPromelaParser(tokens);
		ParserRuleContext tree = parser.stmt();

		StmtContext root = (StmtContext) tree.getRuleContext();
		return root;
	}

	public static StmtContext pareseNanoPromelaString(String nanopromela) {
		NanoPromelaLexer lexer = new NanoPromelaLexer(new ANTLRInputStream(nanopromela));
		CommonTokenStream tokens = new CommonTokenStream(lexer);
		NanoPromelaParser parser = new NanoPromelaParser(tokens);

		StmtContext root = parser.stmt();
		return root;
	}

}
