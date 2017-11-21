package il.ac.bgu.cs.fvm.circuits;

import java.util.Map;
import java.util.Set;

/**
 * An interface for an abstract representation of logic circuits.
 */
public interface Circuit {

    /**
     * Returns a list of names of the input ports.
     *
     * @return the names of the input ports.
     */
    Set<String> getInputPortNames();

    /**
     * Returns the names of the registers.
     *
     * @return the names of the registers.
     */
    Set<String> getRegisterNames();

    /**
     * Return the names of the output ports
     *
     * @return the names of the output ports.
     */
    Set<String> getOutputPortNames();

    /**
     * Calculate register values for the next phase, based on input values
     * and register values at the current phase. All register names must be present. If 
     * the register contains 0, the return value should map its name to {@code false}.
     *
     * @param inputs input values, mapped by input name.
     * @param registers register values, mapped by register name.
     * @return New register values.
     */
    public Map<String,Boolean> updateRegisters(Map<String,Boolean> inputs, Map<String,Boolean> registers);

    /**
     * Calculate output values, based on input and register values. All output port names
     * must be present. If the output port has 0, the return value should map its name to {@code false}.
     *
     * @param inputs A list representing the truth value of each output.
     * @param registers A list representing the truth value of each register.
     * @return Output values.
     */
    public Map<String, Boolean> computeOutputs(Map<String,Boolean> inputs, Map<String,Boolean> registers);
}
