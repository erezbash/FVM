package il.ac.bgu.cs.fvm.transitionsystem;

import java.io.IOException;
import java.io.Reader;
import java.io.Writer;

import javax.xml.parsers.ParserConfigurationException;
import javax.xml.stream.XMLStreamException;

import org.xml.sax.SAXException;

import il.ac.bgu.cs.fvm.exceptions.InvalidTSDescriptionException;

/**
 * 
 * Stores and loads {@link TransitionSystem} objects from XML.
 * 
 */
public interface TransitionSystemXmlFormat {

	TransitionSystem<String,String,String> read(Reader reader) throws Exception;

	void write(TransitionSystem<String,String,String> ts, Writer output) throws InvalidTSDescriptionException, SAXException, ParserConfigurationException, IOException, XMLStreamException;

}
