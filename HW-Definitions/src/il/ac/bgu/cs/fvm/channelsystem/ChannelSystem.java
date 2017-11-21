package il.ac.bgu.cs.fvm.channelsystem;

import java.util.List;

import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;

public class ChannelSystem<L, A> {

    List<ProgramGraph<L, A>> programGraphs;

    public ChannelSystem(List<ProgramGraph<L, A>> programGraphs) {
        this.programGraphs = programGraphs;
    }

    /**
     * @return the programGraphs
     */
    public List<ProgramGraph<L, A>> getProgramGraphs() {
        return programGraphs;
    }

    /**
     * @param programGraphs the programGraphs to set
     */
    public void setProgramGraphs(List<ProgramGraph<L, A>> programGraphs) {
        this.programGraphs = programGraphs;
    }

}
