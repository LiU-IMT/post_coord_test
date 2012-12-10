package se.liu.imt.SCT;

/*    Copyright 2012 Daniel Karlsson

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.*/


/**
 * @author Daniel Karlsson, daniel.karlsson@liu.se
 *
 */

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.StringWriter;
import java.util.Date;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.apache.commons.configuration.Configuration;
import org.apache.commons.configuration.ConfigurationException;
import org.apache.commons.configuration.XMLConfiguration;
import org.apache.log4j.Logger;
import org.apache.log4j.PropertyConfigurator;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.AddAxiom;
import org.semanticweb.owlapi.model.AxiomType;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLException;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyFormat;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.reasoner.OWLReasonerFactory;

public class SCTPostCoordTest {

	private static final Logger log = Logger.getLogger(SCTPostCoordTest.class);
	private static final long twentyFour = 1000*60*60*24;

	/**
	 * @param args
	 * @throws ClassNotFoundException
	 * @throws IllegalAccessException
	 * @throws InstantiationException
	 * @throws ConfigurationException
	 * @throws IOException
	 * @throws OWLException
	 */
	public static void main(String[] args) throws InstantiationException,
			IllegalAccessException, ClassNotFoundException, IOException,
			ConfigurationException, OWLException {

		PropertyConfigurator.configure("log4j.properties");

		Configuration config = null;

		try {
			String configFileName = args[0];
			config = new XMLConfiguration(configFileName);
		} catch (ArrayIndexOutOfBoundsException e) {
			System.err.println("Requires configuration file argument");
			System.exit(-1);
		}

		log.debug("Starting test SNOMED CT post-coordination...");

		// creating ontology manager and loading of SNOMED CT stated form OWL
		// file
		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
		OWLDataFactory dataFactory = manager.getOWLDataFactory();
		final String snomedFileName = config.getString("snomed.OWL_file");
		log.debug("Loading ontology file: " + snomedFileName);
		OWLOntology ontology = manager
				.loadOntologyFromOntologyDocument(new File(snomedFileName));

		log.debug("Loaded " + ontology.getOntologyID());

		// create the reasoner
		final String classifierName = config.getString("classifier.name");
		log.debug("Classifier name: " + classifierName);

		OWLReasonerFactory reasonerFactory = null;
		OWLReasoner reasoner = null;
		final String reasonerFactoryClassName = config
				.getString("classifier.reasoner_factory");
		log.debug("Reasoner factory class: " + reasonerFactoryClassName);
		if (classifierName.equalsIgnoreCase("hermit")) {
			reasonerFactory = new org.semanticweb.HermiT.Reasoner.ReasonerFactory();
		} else
			reasonerFactory = (OWLReasonerFactory) Class.forName(
					reasonerFactoryClassName).newInstance();
		reasoner = reasonerFactory.createReasoner(ontology);
		log.debug("Created reasoner");

		// SNOMED CT IRI string
		final String SNOMED_IRI = "http://www.ihtsdo.org/";

		// create input file reader
		BufferedReader in = null;
		FileWriter out = null;
		try {
			final String inputFileName = config
					.getString("test_parameters.input");
			log.debug("Input file name: " + inputFileName);
			in = new BufferedReader(new FileReader(inputFileName));
			// read past header line
			in.readLine();

			// create output file
			final String outputFileName = config
					.getString("output.file_name_tag");
			out = new FileWriter(outputFileName + "_" + classifierName + "_"
					+ (new Date()).toString());

		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		// get current size in terms of class axioms
		int currentSize = ontology.getAxiomCount(AxiomType.SUBCLASS_OF)
				+ ontology.getAxiomCount(AxiomType.EQUIVALENT_CLASSES);

		final int iterations = config.getInt("test_parameters.iterations");
		final int jumpSize = config.getInt("test_parameters.jump_size");
		final int tries = config.getInt("test_parameters.tries");
		log.debug("Iterations: " + iterations + ", Jump size: " + jumpSize
				+ ", Tries: " + tries);
		
		long startTime = System.currentTimeMillis();
		
		// outer loop for iterations
		for (int i = 0; i <= iterations; i++) {
			
			// break if 24 hours has passed
			if(System.currentTimeMillis() - startTime > twentyFour) {
				log.debug("Ending because time limit has been reached");
				break;
			}


			log.info("Current size: " + currentSize);

			long minTime = Long.MAX_VALUE;

			for (int j = 0; j < tries; j++) {
				long t1 = System.currentTimeMillis();
				// Ask the reasoner to do all the necessary work now
				log.debug("Start classifying...");
				reasoner.precomputeInferences(org.semanticweb.owlapi.reasoner.InferenceType.CLASS_HIERARCHY);
				reasoner.flush();

				// Do special things for special reasoners
				if (classifierName.equalsIgnoreCase("elk")) {
					// nothing special
				} else if (classifierName.equalsIgnoreCase("snorocket")) {
					SnorocketReasoner r = (SnorocketReasoner) reasoner;
					r.synchronizeSnorocket();
				} else if (classifierName.equalsIgnoreCase("fact++")) {
					// nothing special
				} else if (classifierName.equalsIgnoreCase("hermit")) {
					// nothing special
				}
				log.debug("Finished classifying");

				long time = System.currentTimeMillis() - t1;
				if (time < minTime)
					minTime = time;

				log.debug("Finished try: " + (j + 1) + ", Time; " + time);
			}

			log.debug("Finished classifying, Time: " + minTime);
			out.write("" + currentSize + "\t" + minTime + "\n");
			out.flush();

			log.debug("Adding stuff...");

			if (i < iterations)
				// add post-coordinated expressions
				for (int j = 0; j < jumpSize; j++) {
					String line = in.readLine();

					if (line == null)
						break;
					String[] comp = line.split("\t");

					OWLClass new_pc_concept = dataFactory.getOWLClass(IRI
							.create("exp" + (i * jumpSize) + j));

					String baseConcept = comp[0];
					String bodyStructure = comp[1];
					String morphology = comp[2];

					OWLClass baseConceptClass = dataFactory.getOWLClass(IRI
							.create(SNOMED_IRI + "SCT_" + baseConcept));
					OWLClass bodyStructureClass = dataFactory.getOWLClass(IRI
							.create(SNOMED_IRI + "SCT_" + bodyStructure));
					OWLClass morphologyClass = dataFactory.getOWLClass(IRI
							.create(SNOMED_IRI + "SCT_" + morphology));
					OWLObjectProperty roleGroupProp = dataFactory
							.getOWLObjectProperty(IRI.create(SNOMED_IRI
									+ "RoleGroup"));
					OWLObjectProperty findingSiteProp = dataFactory
							.getOWLObjectProperty(IRI.create(SNOMED_IRI
									+ "SCT_363698007"));
					OWLObjectProperty morphologyProp = dataFactory
							.getOWLObjectProperty(IRI.create(SNOMED_IRI
									+ "SCT_116676008"));

					Set<OWLClassExpression> conceptSet = new HashSet<OWLClassExpression>();
					conceptSet.add(dataFactory.getOWLObjectSomeValuesFrom(
							findingSiteProp, bodyStructureClass));
					conceptSet.add(dataFactory.getOWLObjectSomeValuesFrom(
							morphologyProp, morphologyClass));

					OWLClassExpression expr = dataFactory
							.getOWLObjectIntersectionOf(
									baseConceptClass,
									dataFactory.getOWLObjectSomeValuesFrom(
											roleGroupProp,
											dataFactory
													.getOWLObjectIntersectionOf(conceptSet)));

					manager.applyChange(new AddAxiom(ontology, dataFactory
							.getOWLEquivalentClassesAxiom(new_pc_concept, expr)));
				}

			currentSize += jumpSize;

		}

		out.close();

		log.debug("Finished test hopefully successfully");
	}
}
