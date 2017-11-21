package il.ac.bgu.cs.fvm.util;

import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import java.util.ArrayList;
import java.util.Collections;
import static java.util.Collections.emptySet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Function;
import java.util.stream.Collectors;
import static java.util.stream.Collectors.joining;
import static java.util.stream.Collectors.toList;
import javafx.scene.control.cell.MapValueFactory;

/**
 * Takes a {@link TransitionSystem}, makes a Graphviz drawing out of it.
 * @param <A> Type of actions
 * @param <P> Type of atomic propositions
 * @param <S> Type of states
 */
public class GraphvizPainter<S,A,P> {
    
    private final Function<S,String> statePainter; 
    private final Function<A,String> actionPainter; 
    private final Function<P,String> apPainter; 
    private final Map<S,String> idByState = new LinkedHashMap<>();
    
    
    /**
     * A painter that prints the transition system by calling {@link Object#toString()} on its objects.
     * @return A new painter.
     */
    public static GraphvizPainter toStringPainter() {
        return new GraphvizPainter<>(Object::toString,Object::toString,Object::toString);
    }
    
    
    public static GraphvizPainter<Pair<Map<String,Boolean>,Map<String,Boolean>>, Map<String,Boolean>, Object> circuitPainter() {
        return new GraphvizPainter<>(
                (Pair<Map<String,Boolean>,Map<String,Boolean>> state) -> mapValues(state.first) + mapValues(state.second),
                (Map<String,Boolean> act) -> mapValues(act), 
                Object::toString
        );
    }
    
    public GraphvizPainter(Function<S, String> statePainter, Function<A, String> actionPainter, Function<P, String> apPainter) {
        this.statePainter = statePainter;
        this.actionPainter = actionPainter;
        this.apPainter = apPainter;
    }
    
    public String makeDotCode( TransitionSystem<S,A,P> ts ) {
        idByState.clear();
        StringBuilder sb = new StringBuilder();
        sb.append("digraph ts {\n");
        sb.append("graph [label=\"")
          .append( Optional.ofNullable(ts.getName()).orElse("<no name>") )
          .append("\", labelloc=\"t\", fontname=\"Times-Roman\"]\n");
       
        
        int idx=1;
        List<S> sortedStates = new ArrayList<>(ts.getStates());
        Collections.sort(sortedStates, (s1, s2)->statePainter.apply(s1).compareTo(statePainter.apply(s2)));
        for ( S s : sortedStates ) {
            String id = "s"+(idx++);
            idByState.put(s, id);
        }
        
        drawNodes(ts, sb);
        drawTransitions(ts,sb);
        drawAtomicPropositions(ts,sb);
        
        sb.append("}");
        return sb.toString();
    }
    
    private void drawNodes( TransitionSystem<S,A,P> ts, StringBuilder sb ) {
        sb.append("node [shape=box, fontname=\"Courier\"];\n");
        idByState.forEach( (s,id) -> {
            sb.append(id).append("[label=\"")
                    .append( statePainter.apply(s).replace("\"", "\\\"\\") )
                    .append("\"];\n");
            if ( ts.getInitialStates().contains(s) ) {
                String startId = "start_" + id;
                sb.append(startId).append( "[label=\"\", shape=none];\n");
                sb.append(startId).append("->").append(id).append(";\n");
                sb.append("{rank=source; ").append(id).append("; start_").append(id).append("}\n");
            }
        });
    }

    private void drawTransitions(TransitionSystem<S, A, P> ts, StringBuilder sb) {
        sb.append("edge [fontname=\"Courier\"]\n");
        ts.getTransitions().forEach( t -> 
            sb.append( idByState.get(t.getFrom())) 
              .append( " -> " )
              .append( idByState.get(t.getTo()) )
              .append( " [label=\"" )
              .append( actionPainter.apply(t.getAction()).replace("\"", "\\\"\\") )
              .append( "\"];\n" )
        );
    }

    private void drawAtomicPropositions(TransitionSystem<S, A, P> ts, StringBuilder sb) {
        sb.append("node [color=\"#008800\", fontcolor=\"#008800\", shape=note]\n");
        sb.append("edge [color=\"#008800\", arrowhead=none, arrowtail=none, style=dotted]\n");
        
        ts.getStates().stream()
          .filter( s -> ! ts.getLabelingFunction().getOrDefault(s, emptySet()).isEmpty())
          .forEach( s -> {
              // make AP node
              String apNodeId = "ap_" + idByState.get(s);
              String title = ts.getLabelingFunction().get(s).stream().map(apPainter::apply)
                      .collect(Collectors.joining("\\n"));
              sb.append( apNodeId ).append(" [label=\"").append(title).append("\"];\n");
              // connect AP node to s
              sb.append( apNodeId ).append( "->" ).append( idByState.get(s) ).append(";\n");
        });
    }
    
    private static String mapValues(Map<String,Boolean> mp) {
        return  mp.keySet().stream().sorted()
                                    .map(mp::get)
                                    .map( b -> b?"1":"0" ).collect( joining("") );
    }
    
}
