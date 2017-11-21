package il.ac.bgu.cs.fvm.examples;


import il.ac.bgu.cs.fvm.circuits.Circuit;
import java.util.Collections;
import java.util.Map;
import java.util.Set;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.singeltonMap;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.map;

/**
 * The circuit on page 27, Figure 2.2
 */
public class ExampleCircuit implements Circuit {

    /**
     * Implements the relation r = x \/ r
     */
    @Override
    public Map<String, Boolean> updateRegisters(Map<String,Boolean> inputs, Map<String,Boolean> registers) {
        return Collections.singletonMap("r", registers.get("r") || inputs.get("x") );
    }

    /**
     * Implements the relation y = not(x XOR r)
     *
     */
    @Override
    public Map<String, Boolean> computeOutputs(Map<String,Boolean> inputs, Map<String,Boolean> registers) {
        return singeltonMap("y", !(inputs.get("x") ^ registers.get("r")) );
    }

    @Override
    public Set<String> getInputPortNames() {
        return Collections.singleton("x");
    }

    @Override
    public Set<String> getRegisterNames() {
        return Collections.singleton("r");
    }

    @Override
    public Set<String> getOutputPortNames() {
        return Collections.singleton("y");
    }

}
