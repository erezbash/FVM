package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static il.ac.bgu.cs.fvm.util.CollectionHelper.set;

public class ProgramGraphImpl<LOCATION, A> implements ProgramGraph<LOCATION, A> {

    private String name;
    private Set<LOCATION> locations =new HashSet<>();
    private Set<LOCATION> initialStates = new HashSet<>();
    private Set<PGTransition<LOCATION, A>> pgTransitions = new HashSet<>();
    private Set<List<String>> initalizations = new HashSet<>();

    @Override
    public void addInitalization(List<String> init) {
        initalizations.add(init);
    }

    @Override
    public void addInitialLocation(LOCATION location) {
        initialStates.add(location);
    }

    @Override
    public void addLocation(LOCATION l) {
        locations.add(l);
    }

    @Override
    public void addTransition(PGTransition<LOCATION, A> t) {
        pgTransitions.add(t);
    }

    @Override
    public Set<List<String>> getInitalizations() {
        return new HashSet<>(initalizations);
    }

    @Override
    public Set<LOCATION> getInitialLocations() {
        return new HashSet<>(initialStates);
    }

    @Override
    public Set<LOCATION> getLocations() {
        return new HashSet<>(locations);
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public Set<PGTransition<LOCATION, A>> getTransitions() {
        return new HashSet<>(pgTransitions);
    }

    @Override
    public void removeLocation(LOCATION l) {
        locations.remove(l);
    }

    @Override
    public void removeTransition(PGTransition<LOCATION, A> t) { pgTransitions.remove(t);}

    @Override
    public void setName(String name) { this.name = name;}
}
