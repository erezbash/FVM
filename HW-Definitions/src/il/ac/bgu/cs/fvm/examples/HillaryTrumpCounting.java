package il.ac.bgu.cs.fvm.examples;

import static il.ac.bgu.cs.fvm.util.CollectionHelper.p;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.pgtransition;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.seq;
import static java.util.Arrays.asList;

import java.util.List;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;
import il.ac.bgu.cs.fvm.util.Pair;

public class HillaryTrumpCounting {

	static FvmFacade fvmFacadeImpl = FvmFacade.createInstance();

	public static ProgramGraph<String, String> build() {
		ProgramGraph<String, String> pg = fvmFacadeImpl.createProgramGraph();

		asList("counting", "twin", "hwin").forEach(s -> pg.addLocation(s));

		pg.addInitialLocation("counting");

		asList(pgtransition("counting", "t<270 && alabama==0", "atomic{t:=t+9;alabama:=1}", "counting"), pgtransition("counting", "h<270 && alabama==0", "atomic{h:=h+9;alabama:=1}", "counting"), pgtransition("counting", "t<270 && montana==0", "atomic{t:=t+3;montana:=1}", "counting"),
				pgtransition("counting", "h<270 && montana==0", "atomic{h:=h+3;montana:=1}", "counting"), pgtransition("counting", "t<270 && alaska==0", "atomic{t:=t+3;alaska:=1}", "counting"), pgtransition("counting", "h<270 && alaska==0", "atomic{h:=h+3;alaska:=1}", "counting"),
				pgtransition("counting", "t<270 && nebraska==0", "atomic{t:=t+5;nebraska:=1}", "counting"), pgtransition("counting", "h<270 && nebraska==0", "atomic{h:=h+5;nebraska:=1}", "counting"), pgtransition("counting", "t<270 && arizona==0", "atomic{t:=t+11;arizona:=1}", "counting"),
				pgtransition("counting", "h<270 && arizona==0", "atomic{h:=h+11;arizona:=1}", "counting"), pgtransition("counting", "t<270 && nevada==0", "atomic{t:=t+6;nevada:=1}", "counting"), pgtransition("counting", "h<270 && nevada==0", "atomic{h:=h+6;nevada:=1}", "counting"),
				pgtransition("counting", "t<270 && arkansas==0", "atomic{t:=t+6;arkansas:=1}", "counting"), pgtransition("counting", "h<270 && arkansas==0", "atomic{h:=h+6;arkansas:=1}", "counting"), pgtransition("counting", "t<270 && newHampshire==0", "atomic{t:=t+4;newHampshire:=1}", "counting"),
				pgtransition("counting", "h<270 && newHampshire==0", "atomic{h:=h+4;newHampshire:=1}", "counting"), pgtransition("counting", "t<270 && california==0", "atomic{t:=t+55;california:=1}", "counting"),
				pgtransition("counting", "h<270 && california==0", "atomic{h:=h+55;california:=1}", "counting"), pgtransition("counting", "t<270 && newJersey==0", "atomic{t:=t+14;newJersey:=1}", "counting"),
				pgtransition("counting", "h<270 && newJersey==0", "atomic{h:=h+14;newJersey:=1}", "counting"), pgtransition("counting", "t<270 && colorado==0", "atomic{t:=t+9;colorado:=1}", "counting"), pgtransition("counting", "h<270 && colorado==0", "atomic{h:=h+9;colorado:=1}", "counting"),
				pgtransition("counting", "t<270 && newMexico==0", "atomic{t:=t+5;newMexico:=1}", "counting"), pgtransition("counting", "h<270 && newMexico==0", "atomic{h:=h+5;newMexico:=1}", "counting"),
				pgtransition("counting", "t<270 && connecticut==0", "atomic{t:=t+7;connecticut:=1}", "counting"), pgtransition("counting", "h<270 && connecticut==0", "atomic{h:=h+7;connecticut:=1}", "counting"),
				pgtransition("counting", "t<270 && newYork==0", "atomic{t:=t+29;newYork:=1}", "counting"), pgtransition("counting", "h<270 && newYork==0", "atomic{h:=h+29;newYork:=1}", "counting"), pgtransition("counting", "t<270 && delaware==0", "atomic{t:=t+3;delaware:=1}", "counting"),
				pgtransition("counting", "h<270 && delaware==0", "atomic{h:=h+3;delaware:=1}", "counting"), pgtransition("counting", "t<270 && northCarolina==0", "atomic{t:=t+15;northCarolina:=1}", "counting"),
				pgtransition("counting", "h<270 && northCarolina==0", "atomic{h:=h+15;northCarolina:=1}", "counting"), pgtransition("counting", "t<270 && florida==0", "atomic{t:=t+29;florida:=1}", "counting"), pgtransition("counting", "h<270 && florida==0", "atomic{h:=h+29;florida:=1}", "counting"),
				pgtransition("counting", "t<270 && northDakota==0", "atomic{t:=t+3;northDakota:=1}", "counting"), pgtransition("counting", "h<270 && northDakota==0", "atomic{h:=h+3;northDakota:=1}", "counting"),
				pgtransition("counting", "t<270 && georgia==0", "atomic{t:=t+16;georgia:=1}", "counting"), pgtransition("counting", "h<270 && georgia==0", "atomic{h:=h+16;georgia:=1}", "counting"), pgtransition("counting", "t<270 && ohio==0", "atomic{t:=t+18;ohio:=1}", "counting"),
				pgtransition("counting", "h<270 && ohio==0", "atomic{h:=h+18;ohio:=1}", "counting"), pgtransition("counting", "t<270 && hawaii==0", "atomic{t:=t+4;hawaii:=1}", "counting"), pgtransition("counting", "h<270 && hawaii==0", "atomic{h:=h+4;hawaii:=1}", "counting"),
				pgtransition("counting", "t<270 && oklahoma==0", "atomic{t:=t+7;oklahoma:=1}", "counting"), pgtransition("counting", "h<270 && oklahoma==0", "atomic{h:=h+7;oklahoma:=1}", "counting"), pgtransition("counting", "t<270 && idaho==0", "atomic{t:=t+4;idaho:=1}", "counting"),
				pgtransition("counting", "h<270 && idaho==0", "atomic{h:=h+4;idaho:=1}", "counting"), pgtransition("counting", "t<270 && oregon==0", "atomic{t:=t+7;oregon:=1}", "counting"), pgtransition("counting", "h<270 && oregon==0", "atomic{h:=h+7;oregon:=1}", "counting"),
				pgtransition("counting", "t<270 && illinois==0", "atomic{t:=t+20;illinois:=1}", "counting"), pgtransition("counting", "h<270 && illinois==0", "atomic{h:=h+20;illinois:=1}", "counting"),
				pgtransition("counting", "t<270 && pennsylvania==0", "atomic{t:=t+20;pennsylvania:=1}", "counting"), pgtransition("counting", "h<270 && pennsylvania==0", "atomic{h:=h+20;pennsylvania:=1}", "counting"),
				pgtransition("counting", "t<270 && indiana==0", "atomic{t:=t+11;indiana:=1}", "counting"), pgtransition("counting", "h<270 && indiana==0", "atomic{h:=h+11;indiana:=1}", "counting"), pgtransition("counting", "t<270 && rhodeIsland==0", "atomic{t:=t+4;rhodeIsland:=1}", "counting"),
				pgtransition("counting", "h<270 && rhodeIsland==0", "atomic{h:=h+4;rhodeIsland:=1}", "counting"), pgtransition("counting", "t<270 && iowa==0", "atomic{t:=t+6;iowa:=1}", "counting"), pgtransition("counting", "h<270 && iowa==0", "atomic{h:=h+6;iowa:=1}", "counting"),
				pgtransition("counting", "t<270 && southCarolina==0", "atomic{t:=t+9;southCarolina:=1}", "counting"), pgtransition("counting", "h<270 && southCarolina==0", "atomic{h:=h+9;southCarolina:=1}", "counting"),
				pgtransition("counting", "t<270 && kansas==0", "atomic{t:=t+6;kansas:=1}", "counting"), pgtransition("counting", "h<270 && kansas==0", "atomic{h:=h+6;kansas:=1}", "counting"), pgtransition("counting", "t<270 && southDakota==0", "atomic{t:=t+3;southDakota:=1}", "counting"),
				pgtransition("counting", "h<270 && southDakota==0", "atomic{h:=h+3;southDakota:=1}", "counting"), pgtransition("counting", "t<270 && kentucky==0", "atomic{t:=t+8;kentucky:=1}", "counting"), pgtransition("counting", "h<270 && kentucky==0", "atomic{h:=h+8;kentucky:=1}", "counting"),
				pgtransition("counting", "t<270 && tennessee==0", "atomic{t:=t+11;tennessee:=1}", "counting"), pgtransition("counting", "h<270 && tennessee==0", "atomic{h:=h+11;tennessee:=1}", "counting"), pgtransition("counting", "t<270 && louisiana==0", "atomic{t:=t+8;louisiana:=1}", "counting"),
				pgtransition("counting", "h<270 && louisiana==0", "atomic{h:=h+8;louisiana:=1}", "counting"), pgtransition("counting", "t<270 && texas==0", "atomic{t:=t+38;texas:=1}", "counting"), pgtransition("counting", "h<270 && texas==0", "atomic{h:=h+38;texas:=1}", "counting"),
				pgtransition("counting", "t<270 && maine==0", "atomic{t:=t+4;maine:=1}", "counting"), pgtransition("counting", "h<270 && maine==0", "atomic{h:=h+4;maine:=1}", "counting"), pgtransition("counting", "t<270 && utah==0", "atomic{t:=t+6;utah:=1}", "counting"),
				pgtransition("counting", "h<270 && utah==0", "atomic{h:=h+6;utah:=1}", "counting"), pgtransition("counting", "t<270 && maryland==0", "atomic{t:=t+10;maryland:=1}", "counting"), pgtransition("counting", "h<270 && maryland==0", "atomic{h:=h+10;maryland:=1}", "counting"),
				pgtransition("counting", "t<270 && vermont==0", "atomic{t:=t+3;vermont:=1}", "counting"), pgtransition("counting", "h<270 && vermont==0", "atomic{h:=h+3;vermont:=1}", "counting"), pgtransition("counting", "t<270 && massachusetts==0", "atomic{t:=t+11;massachusetts:=1}", "counting"),
				pgtransition("counting", "h<270 && massachusetts==0", "atomic{h:=h+11;massachusetts:=1}", "counting"), pgtransition("counting", "t<270 && virginia==0", "atomic{t:=t+13;virginia:=1}", "counting"),
				pgtransition("counting", "h<270 && virginia==0", "atomic{h:=h+13;virginia:=1}", "counting"), pgtransition("counting", "t<270 && michigan==0", "atomic{t:=t+16;michigan:=1}", "counting"), pgtransition("counting", "h<270 && michigan==0", "atomic{h:=h+16;michigan:=1}", "counting"),
				pgtransition("counting", "t<270 && washington==0", "atomic{t:=t+12;washington:=1}", "counting"), pgtransition("counting", "h<270 && washington==0", "atomic{h:=h+12;washington:=1}", "counting"),
				pgtransition("counting", "t<270 && minnesota==0", "atomic{t:=t+10;minnesota:=1}", "counting"), pgtransition("counting", "h<270 && minnesota==0", "atomic{h:=h+10;minnesota:=1}", "counting"),
				pgtransition("counting", "t<270 && westVirginia==0", "atomic{t:=t+5;westVirginia:=1}", "counting"), pgtransition("counting", "h<270 && westVirginia==0", "atomic{h:=h+5;westVirginia:=1}", "counting"),
				pgtransition("counting", "t<270 && mississippi==0", "atomic{t:=t+6;mississippi:=1}", "counting"), pgtransition("counting", "h<270 && mississippi==0", "atomic{h:=h+6;mississippi:=1}", "counting"),
				pgtransition("counting", "t<270 && wisconsin==0", "atomic{t:=t+10;wisconsin:=1}", "counting"), pgtransition("counting", "h<270 && wisconsin==0", "atomic{h:=h+10;wisconsin:=1}", "counting"), pgtransition("counting", "t<270 && missouri==0", "atomic{t:=t+10;missouri:=1}", "counting"),
				pgtransition("counting", "h<270 && missouri==0", "atomic{h:=h+10;missouri:=1}", "counting"), pgtransition("counting", "t<270 && wyoming==0", "atomic{t:=t+3;wyoming:=1}", "counting"), pgtransition("counting", "h<270 && wyoming==0", "atomic{h:=h+3;wyoming:=1}", "counting"))
						.forEach(t -> pg.addTransition(t));

		pg.addInitalization(asList("t:=0", "h:=0", "alabama:=0", "montana:=0", "alaska:=0", "nebraska:=0", "arizona:=0", "nevada:=0", "arkansas:=0", "newHampshire:=0", "california:=0", "newJersey:=0", "colorado:=0", "newMexico:=0", "connecticut:=0", "newYork:=0", "delaware:=0", "northCarolina:=0",
				"florida:=0", "northDakota:=0", "georgia:=0", "ohio:=0", "hawaii:=0", "oklahoma:=0", "idaho:=0", "oregon:=0", "illinois:=0", "pennsylvania:=0", "indiana:=0", "rhodeIsland:=0", "iowa:=0", "southCarolina:=0", "kansas:=0", "southDakota:=0", "kentucky:=0", "tennessee:=0", "louisiana:=0",
				"texas:=0", "maine:=0", "utah:=0", "maryland:=0", "vermont:=0", "massachusetts:=0", "virginia:=0", "michigan:=0", "washington:=0", "minnesota:=0", "westVirginia:=0", "mississippi:=0", "wisconsin:=0", "missouri:=0", "wyoming:=0"));

		return pg;
	}

	public static ProgramGraph<String, String> buildSmall() {
		ProgramGraph<String, String> pg = fvmFacadeImpl.createProgramGraph();

		asList("counting", "twin", "hwin").forEach(s -> pg.addLocation(s));

		pg.addInitialLocation("counting");

		asList(pgtransition("counting", "t<270 && alabama==0", "atomic{t:=t+9;alabama:=1}", "counting"), pgtransition("counting", "h<270 && alabama==0", "atomic{h:=h+9;alabama:=1}", "counting"), pgtransition("counting", "t<270 && montana==0", "atomic{t:=t+3;montana:=1}", "counting"),
				pgtransition("counting", "h<270 && montana==0", "atomic{h:=h+3;montana:=1}", "counting"), pgtransition("counting", "t<270 && alaska==0", "atomic{t:=t+3;alaska:=1}", "counting"), pgtransition("counting", "h<270 && alaska==0", "atomic{h:=h+3;alaska:=1}", "counting"),
				pgtransition("counting", "t<270 && nebraska==0", "atomic{t:=t+5;nebraska:=1}", "counting"), pgtransition("counting", "h<270 && nebraska==0", "atomic{h:=h+5;nebraska:=1}", "counting"), pgtransition("counting", "t<270 && arizona==0", "atomic{t:=t+11;arizona:=1}", "counting"),
				pgtransition("counting", "h<270 && arizona==0", "atomic{h:=h+11;arizona:=1}", "counting"), pgtransition("counting", "t<270 && nevada==0", "atomic{t:=t+6;nevada:=1}", "counting"), pgtransition("counting", "h<270 && nevada==0", "atomic{h:=h+6;nevada:=1}", "counting"),
				pgtransition("counting", "t<270 && arkansas==0", "atomic{t:=t+6;arkansas:=1}", "counting"), pgtransition("counting", "h<270 && arkansas==0", "atomic{h:=h+6;arkansas:=1}", "counting"), pgtransition("counting", "t<270 && newHampshire==0", "atomic{t:=t+4;newHampshire:=1}", "counting"),
				pgtransition("counting", "h<270 && newHampshire==0", "atomic{h:=h+4;newHampshire:=1}", "counting"), pgtransition("counting", "t<270 && california==0", "atomic{t:=t+55;california:=1}", "counting"),
				pgtransition("counting", "h<270 && california==0", "atomic{h:=h+55;california:=1}", "counting"), pgtransition("counting", "t<270 && newJersey==0", "atomic{t:=t+14;newJersey:=1}", "counting"),
				pgtransition("counting", "h<270 && newJersey==0", "atomic{h:=h+14;newJersey:=1}", "counting")).forEach(t -> pg.addTransition(t));

		pg.addInitalization(asList("alabama:=0", "montana:=0", "alaska:=0", "nebraska:=0", "arizona:=0", "nevada:=0", "arkansas:=0", "newHampshire:=0", "california:=0", "newJersey:=0"));

		return pg;

	}

	@SuppressWarnings("unchecked")
	// @Test
	public void genCode() {
		List<Pair<String, Integer>> l = seq(p("alabama", 9), p("montana", 3), p("alaska", 3), p("nebraska", 5), p("arizona", 11), p("nevada", 6), p("arkansas", 6), p("newHampshire", 4), p("california", 55), p("newJersey", 14), p("colorado", 9), p("newMexico", 5), p("connecticut", 7),
				p("newYork", 29), p("delaware", 3), p("northCarolina", 15), p("florida", 29), p("northDakota", 3), p("georgia", 16), p("ohio", 18), p("hawaii", 4), p("oklahoma", 7), p("idaho", 4), p("oregon", 7), p("illinois", 20), p("pennsylvania", 20), p("indiana", 11), p("rhodeIsland", 4),
				p("iowa", 6), p("southCarolina", 9), p("kansas", 6), p("southDakota", 3), p("kentucky", 8), p("tennessee", 11), p("louisiana", 8), p("texas", 38), p("maine", 4), p("utah", 6), p("maryland", 10), p("vermont", 3), p("massachusetts", 11), p("virginia", 13), p("michigan", 16),
				p("washington", 12), p("minnesota", 10), p("westVirginia", 5), p("mississippi", 6), p("wisconsin", 10), p("missouri", 10), p("wyoming", 3));

		for (Pair<String, Integer> x : l.subList(0, 10)) {
			System.out.println("pgtransition(\"counting\", \"t<270 && " + x.getFirst() + "==0\", \"atomic{t:=t+" + x.getSecond() + ";" + x.getFirst() + ":=1}\", \"counting\"),");
			System.out.println("pgtransition(\"counting\", \"h<270 && " + x.getFirst() + "==0\", \"atomic{h:=h+" + x.getSecond() + ";" + x.getFirst() + ":=1}\", \"counting\"),");
		}

		for (Pair<String, Integer> x : l.subList(0, 10)) {
			System.out.println("\"" + x.getFirst() + ":=0\",");
		}
	}

}
