package il.ac.bgu.cs.fvm.channelsystem;

import java.util.Map;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;

import il.ac.bgu.cs.fvm.nanopromela.Evaluator;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaLexer;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaParser;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaParser.JoinedContext;
import il.ac.bgu.cs.fvm.programgraph.ThrowingErrorListener;

/**
 * A class for identifying and interpreting combined actions such as 
 * {@code _C!0 | _C?x}. As in this example, joined actions involve reading and
 * writing to channels with zero capacity separated by the '|' character.
 * Channels with zero capacity are marked by an underscore in front of 
 * the channel name.
 */
public class ParserBasedInterleavingActDef implements InterleavingActDef {

    @Override
    public Map<String, Object> effect(Map<String, Object> eval, Object action) {
        if (action.equals("")) {
            return eval;
        }

        try {
            return new Evaluator(eval).evaluate(parseAction((String) action));
        } catch (Exception e) {
            e.printStackTrace();
            return null;
        }
    }

    /**
     * Parse a string and build a parse tree for a joined action.
     *
     * @param action The string to parse.
     *
     * @return The root of the parse tree or null if cannot parse.
     */
    private JoinedContext parseAction(String action) {
        NanoPromelaLexer lexer = new NanoPromelaLexer(new ANTLRInputStream(action));

        CommonTokenStream tokens = new CommonTokenStream(lexer);
        NanoPromelaParser parser = new NanoPromelaParser(tokens);

        lexer.removeErrorListeners();
        lexer.addErrorListener(new ThrowingErrorListener());

        parser.removeErrorListeners();
        parser.addErrorListener(new ThrowingErrorListener());

        try {
            JoinedContext p = parser.joined();

            if (parser.isMatchedEOF()) {
                return p;
            } else {
                return null;
            }

        } catch (Exception ex) {
            return null;
        }
    }

    @Override
    public boolean isMatchingAction(Object action) {
        return action.equals("") || parseAction((String) action) != null;
    }

    @Override
    public boolean isOneSidedAction(String action) {
        NanoPromelaLexer lexer = new NanoPromelaLexer(new ANTLRInputStream(action));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        NanoPromelaParser parser = new NanoPromelaParser(tokens);

        lexer.removeErrorListeners();
        lexer.addErrorListener(new ThrowingErrorListener());

        parser.removeErrorListeners();
        parser.addErrorListener(new ThrowingErrorListener());

        try {
            parser.onesided();
            return parser.isMatchedEOF();
        } catch (Exception e) {
            return false;
        }

    }
}
