package il.ac.bgu.cs.fvm.examples;

import il.ac.bgu.cs.fvm.FvmFacade;
import static java.util.Arrays.asList;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import il.ac.bgu.cs.fvm.programgraph.ActionDef;
import il.ac.bgu.cs.fvm.programgraph.ConditionDef;
import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;

public class ExtendedVendingMachineBuilder {

    static int max = 2;

    public static ProgramGraph<String, String> build() {
        ProgramGraph<String, String> pg = FvmFacade.createInstance().createProgramGraph();

        String start = "start";
        String select = "select";

        pg.addLocation(start);
        pg.addLocation(select);

        pg.addInitialLocation(start);

        pg.addTransition(new PGTransition<>(start, "true", "coin", select));
        pg.addTransition(new PGTransition<>(start, "true", "refill", start));
        pg.addTransition(new PGTransition<>(select, "nsoda > 0", "sget", start));
        pg.addTransition(new PGTransition<>(select, "nbeer > 0", "bget", start));
        pg.addTransition(new PGTransition<>(select, "nbeer = 0 && nsoda = 0", "ret_coin", start));

        pg.addInitalization(asList("refill"));

        return pg;

    }

    public static Set<ConditionDef> getConditionDefs() {

        Set<ConditionDef> cond = new HashSet<>();

        // Define the true condition
        cond.add( (eval,condition) -> condition.equals("true") );

        // Define the > 0 condition
        cond.add(new ConditionDef() {
            Pattern r = Pattern.compile("^(\\S*)\\s*>\\s*0\\s*$");

            @Override
            public boolean evaluate(Map<String, Object> eval, String condition) {

                Matcher m = r.matcher(condition);

                if (m.matches()) {

                    return (int) eval.get(m.group(1)) > 0;
                } else {
                    return false;
                }
            }
        });

        // Define the x = 0 && y = 0 condition
        cond.add(new ConditionDef() {
            @Override
            public boolean evaluate(Map<String, Object> eval, String condition) {
                if (condition.equals("nbeer = 0 && nsoda = 0")) {
                    return ((int) eval.get("nsoda") == 0) && ((int) eval.get("nbeer") == 0);
                } else {
                    return false;
                }
            }
        });

        return cond;
    }

    @SuppressWarnings("serial")
    public static Set<ActionDef> getActionDefs() {
        Set<ActionDef> effect = new HashSet<>();

        // Define the refill action
        effect.add(new ActionDef() {
            @Override
            public boolean isMatchingAction(Object candidate) {
                return candidate.equals("refill");
            }

            @Override
            public Map<String, Object> effect(Map<String, Object> eval,
                                              Object action) {
                return new HashMap<String, Object>(eval) {
                    {
                        put("nsoda", max);
                        put("nbeer", max);
                    }
                };
            }

        });

        // Define the sget action
        effect.add(new ActionDef() {
            @Override
            public boolean isMatchingAction(Object action) {
                return action.equals("sget");
            }

            @Override
            public Map<String, Object> effect(Map<String, Object> eval,
                                              Object action) {
                return new HashMap<String, Object>(eval) {
                    {
                        put("nsoda", ((int) eval.get("nsoda")) - 1);
                    }
                };
            }

        });

        // Define the bget action
        effect.add(new ActionDef() {
            @Override
            public boolean isMatchingAction(Object action) {
                return action.equals("bget");
            }

            @Override
            public Map<String, Object> effect(Map<String, Object> eval,
                                              Object action) {
                return new HashMap<String, Object>(eval) {
                    {
                        put("nbeer", ((int) eval.get("nbeer")) - 1);
                    }
                };
            }

        });

        return effect;
    }
}
