package il.ac.bgu.cs.fvm.transitionsystem;

import il.ac.bgu.cs.fvm.FvmFacade;
import java.io.IOException;
import java.io.Reader;
import java.io.Writer;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicReference;

import javax.xml.parsers.ParserConfigurationException;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;
import javax.xml.stream.XMLOutputFactory;
import javax.xml.stream.XMLStreamException;
import javax.xml.stream.XMLStreamWriter;

import org.xml.sax.Attributes;
import org.xml.sax.ContentHandler;
import org.xml.sax.InputSource;
import org.xml.sax.Locator;
import org.xml.sax.SAXException;
import org.xml.sax.XMLReader;

import il.ac.bgu.cs.fvm.exceptions.FVMException;
import il.ac.bgu.cs.fvm.exceptions.InvalidTSDescriptionException;
import il.ac.bgu.cs.fvm.exceptions.InvalidXmlException;
import il.ac.bgu.cs.fvm.exceptions.TransitionSystemPart;

/**
 * Converts {@link TransitionSystem} objects to XML format and vice versa.
 * 
 */
public class StAXTransitionSystemXmlFormat implements TransitionSystemXmlFormat {

	static final String kTransitionSystem = "transitionSystem";
	static final String kName = "Name";
	static final String kStates = "states";
	static final String kState = "state";
	static final String kActions = "actions";
	static final String kAction = "action";
	static final String kEntry = "entry";
	static final String kAtomicPropositions = "atomicPropositions";
	static final String kAtomicProposition = "atomicProposition";
	static final String kInitialStates = "initialStates";
	static final String kInitialState = "initialState";
	static final String kLabelingFunction = "labelingFunction";
	static final String kLabel = "label";
	static final String kTransitions = "transitions";
	static final String kTransition = "transition";
	static final String attSId = "sId";
	static final String attAId = "aId";
	static final String attApId = "apId";
	static final String attState = "state";
	static final String attAction = "action";
	static final String attAP = "atomicProposition";
	static final String attFrom = "from";
	static final String attTo = "to";

	@SuppressWarnings({ "rawtypes", "unchecked" })
	@Override
	public void write(TransitionSystem ts, Writer output) throws XMLStreamException {
		write(ts, XMLOutputFactory.newFactory().createXMLStreamWriter(output));
	}

	protected void write(TransitionSystem<String,String,String> ts, XMLStreamWriter out) throws XMLStreamException {
		Map<String, String> apIdMap = new HashMap<>();

		out.writeStartDocument();
		out.writeStartElement(kTransitionSystem);

		if (ts.getName() != null) {
			out.writeStartElement(kName);
			out.writeCharacters(ts.getName());
			out.writeEndElement();
		}

		out.writeStartElement(kStates);
		ts.getStates().forEach(s -> wrapExceptions(() -> {
			out.writeEmptyElement(kState);
			out.writeAttribute(attSId, s);
		}));
		out.writeEndElement();

		out.writeStartElement(kActions);
		ts.getActions().forEach(act -> wrapExceptions(() -> {
			out.writeEmptyElement(kAction);
			out.writeAttribute(attAId, act);
		}));
		out.writeEndElement();

		out.writeStartElement(kAtomicPropositions);
		ts.getAtomicPropositions().forEach(ap -> wrapExceptions(() -> {
			apIdMap.put(ap, "ap" + (apIdMap.size() + 1));

			out.writeStartElement(kAtomicProposition);
			out.writeAttribute(attApId, apIdMap.get(ap));
			out.writeCharacters(ap);
			out.writeEndElement();
		}));
		out.writeEndElement();

		out.writeStartElement(kInitialStates);
		ts.getInitialStates().forEach(istt -> wrapExceptions(() -> {
			out.writeEmptyElement(kInitialState);
			out.writeAttribute(attState, istt);
		}));
		out.writeEndElement();

		out.writeStartElement(kLabelingFunction);
		ts.getLabelingFunction().entrySet().forEach(ent -> wrapExceptions(() -> {
			out.writeStartElement(kEntry);
			out.writeAttribute(attState, ent.getKey());
			ent.getValue().forEach(lbl -> wrapExceptions(() -> {
				out.writeEmptyElement(kLabel);
				out.writeAttribute(attAP, apIdMap.get(lbl));
			}));
			out.writeEndElement();
		}));
		out.writeEndElement();

		out.writeStartElement(kTransitions);
		ts.getTransitions().forEach(t -> wrapExceptions(() -> {
			out.writeEmptyElement(kTransition);
			out.writeAttribute(attFrom, t.getFrom());
			out.writeAttribute(attAction, t.getAction());
			out.writeAttribute(attTo, t.getTo());
		}));

		out.writeEndElement();

		out.writeEndDocument();
	}

	@Override
	public TransitionSystem<String, String, String> read(Reader characterReader) throws InvalidTSDescriptionException, SAXException, ParserConfigurationException, IOException {
		SAXParserFactory fact = SAXParserFactory.newInstance();
		SAXParser parser = fact.newSAXParser();
		XMLReader xmlReader = parser.getXMLReader();

		final AtomicReference<TransitionSystem<String, String, String>> tsRef = new AtomicReference<>();
		final List<FVMException> errors = new LinkedList<>();

		xmlReader.setContentHandler(new ContentHandler() {

			TransitionSystem<String, String, String> ts;
			private Locator docLoc;
			private StringBuilder sb;
			private String apId;
			private String labeledState;

			@Override
			public void setDocumentLocator(Locator locator) {
				docLoc = locator;
			}

			@Override
			public void startDocument() throws SAXException {
				sb = new StringBuilder();
			}

			@Override
			public void endDocument() throws SAXException {
			}

			@Override
			public void startPrefixMapping(String prefix, String uri) throws SAXException {
			}

			@Override
			public void endPrefixMapping(String prefix) throws SAXException {
			}

			@Override
			public void startElement(String uri, String localName, String qName, Attributes atts) throws SAXException {
				switch (qName) {
				case kTransitionSystem:
					ts = FvmFacade.createInstance().createTransitionSystem();
					break;

				case kAction:
					String actionId = atts.getValue(attAId);
					if (actionId != null) {
						ts.addAction(actionId);
					} else {
						errors.add(new InvalidXmlException(loc() + " missing " + attAId + " attribute", TransitionSystemPart.ACTIONS));
					}
					break;

				case kState:
					String stateId = atts.getValue(attSId);
					if (stateId != null) {
						ts.addState(stateId);
					} else {
						errors.add(new InvalidXmlException(loc() + " missing " + attSId + " attribute", TransitionSystemPart.STATES));
					}
					break;

				case kAtomicProposition:
					apId = atts.getValue(attApId);
					if (apId == null) {
						errors.add(new InvalidXmlException(loc() + " missing " + attApId + " attribute", TransitionSystemPart.ATOMIC_PROPOSITIONS));
					}
					break;

				case kInitialState:
					try {
						ts.addInitialState(atts.getValue(attState));
					} catch (FVMException e) {
						errors.add(e);
					}
					break;

				case kEntry:
					labeledState = atts.getValue(attState);
					if (labeledState == null) {
						errors.add(new InvalidXmlException(loc() + " missing " + attState + " attribute", TransitionSystemPart.ATOMIC_PROPOSITIONS));
					}
					break;

				case kLabel:
					String propId = atts.getValue(attAP);
					if (propId == null) {
						errors.add(new InvalidXmlException(loc() + " missing " + attAP + " attribute", TransitionSystemPart.LABELING_FUNCTION));
					} else {
						try {
							ts.addToLabel(labeledState, propId);
						} catch (FVMException fe) {
							errors.add(fe);
						}
					}
					break;

				case kTransition:
					String from = atts.getValue(attFrom);
					String action = atts.getValue(attAction);
					String to = atts.getValue(attTo);

					if (from == null || action == null || to == null) {
						errors.add(new InvalidXmlException(loc() + " transition node should have attributes " + attFrom + ", " + attAction + ", and " + attTo, TransitionSystemPart.TRANSITIONS));
					} else {
						try {
							ts.addTransition(new Transition<>(from, action, to));
						} catch (FVMException fe) {
							errors.add(fe);
						}
					}
				}
			}

			@Override
			public void endElement(String uri, String localName, String qName) throws SAXException {
				switch (qName) {
				case kTransitionSystem:
					tsRef.set(ts);
					break;

				case kName:
					ts.setName(sb.toString().trim());
					sb.setLength(0);
					break;

				case kAtomicProposition:
					String proposition = sb.toString().trim();
					ts.addAtomicProposition(proposition);
					sb.setLength(0);
					apId = null;
					break;

				case kEntry:
					labeledState = null;
					break;
				}
			}

			@Override
			public void characters(char[] ch, int start, int length) throws SAXException {
				sb.append(ch, start, length);
			}

			@Override
			public void ignorableWhitespace(char[] ch, int start, int length) throws SAXException {
			}

			@Override
			public void processingInstruction(String target, String data) throws SAXException {
			}

			@Override
			public void skippedEntity(String name) throws SAXException {
			}

			private String loc() {
				return "[" + docLoc.getLineNumber() + ": " + docLoc.getColumnNumber() + "]";
			}
		});

		xmlReader.parse(new InputSource(characterReader));

		if (errors.isEmpty()) {
			return tsRef.get();
		} else {
			throw new InvalidTSDescriptionException(errors);
		}
	}

	@FunctionalInterface
	public static interface ThrowingFunction<R> {
		R apply() throws Exception;
	}

	@FunctionalInterface
	public static interface VoidThrowingFunction {
		void apply() throws Exception;
	}

	public static <R> R wrapExceptions(ThrowingFunction<R> func) {
		try {
			return func.apply();
		} catch (Exception e) {
			throw new RuntimeException(e);
		}
	}

	
	public static void wrapExceptions(VoidThrowingFunction func) {
		try {
			func.apply();
		} catch (Exception e) {
			throw new RuntimeException(e);
		}
	}

}
