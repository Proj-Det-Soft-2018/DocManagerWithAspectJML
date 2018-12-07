package business.service;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.StringReader;
import java.io.StringWriter;
import java.net.URI;
import java.net.URL;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.sax.SAXResult;
import javax.xml.transform.stream.StreamResult;
import javax.xml.transform.stream.StreamSource;
import org.apache.commons.io.IOUtils;
import org.apache.fop.apps.FOPException;
import org.apache.fop.apps.FOUserAgent;
import org.apache.fop.apps.Fop;
import org.apache.fop.apps.FopFactory;
import org.apache.fop.apps.MimeConstants;
import org.apache.log4j.Logger;
import org.w3c.dom.Document;
import org.w3c.dom.Element;


public class XmlToPdfAdapter {

  private static final /*@ spec_public nullable @*/ URL FO_TEMPLATE_PATH = XmlToPdfAdapter.class.getResource("/fo_templates/xml2fo.xsl");
  private static final /*@ spec_public nullable @*/ Logger LOGGER = Logger.getLogger(XmlToPdfAdapter.class);

  // Subsídios para geração de PDF -- Apache Xalan/FOP
  private /*@ spec_public nullable @*/ Transformer xmlToFoTransformer;
  private /*@ spec_public nullable @*/ FopFactory fopFactory;
  private /*@ spec_public nullable @*/ FOUserAgent foUserAgent;

  public XmlToPdfAdapter() {
    xmlToFoTransformer = generateTransformer();
    fopFactory = generateFopFactory();
    foUserAgent = generateFOUserAgent();
  }

  /*@ 
  @    ensures \result != null;
  @  also
  @    ensures \result == null;
  @*/
  private Transformer generateTransformer() {

    try {
      TransformerFactory tf = TransformerFactory.newInstance();
      DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
      dbf.setNamespaceAware(true);

      DocumentBuilder db = dbf.newDocumentBuilder();
      Document xslDoc = db.parse(FO_TEMPLATE_PATH.openStream());
      DOMSource xslSource = new DOMSource(xslDoc);

      return tf.newTransformer(xslSource);
    } catch (Exception e) {
      LOGGER.error(e.getMessage(), e);
      return null;
    }
  }

  private FopFactory generateFopFactory() {

    FopFactory newFopFactory = null;
    String path = FO_TEMPLATE_PATH.getPath();
    String folderPath = "file://" + path.substring(0, path.lastIndexOf("/fo_templates/xml2fo.xsl"));

    File config = new File("../src/main/resources/fop.xconf");

    try (ByteArrayOutputStream outputStream = new ByteArrayOutputStream()) {
      // Lê o arquivo de configuração do FOP e seta o campo <base> para a pasta "resources"
      DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
      DocumentBuilder db = dbf.newDocumentBuilder();
      Document fopConfDoc = db.parse(config);
      Element element = (Element) fopConfDoc.getElementsByTagName("base").item(0);
      element.setTextContent(folderPath);

      // Transforma o w3c.Document em InputStream
      DOMSource xmlSource = new DOMSource(fopConfDoc);
      StreamResult outputTarget = new StreamResult(outputStream);
      TransformerFactory.newInstance().newTransformer().transform(xmlSource, outputTarget);
      InputStream inputStream = new ByteArrayInputStream(outputStream.toByteArray());

      // Gera a fábrica com o arquivo de configuração
      newFopFactory = FopFactory.newInstance(new URI(folderPath), inputStream);
      inputStream.close();

    } catch (Exception e) {
      LOGGER.error(e.getMessage(), e);
    }

    return newFopFactory;
  }

  private FOUserAgent generateFOUserAgent() {
    FOUserAgent newFOUserAgent = null;

    if (this.fopFactory != null) {
      newFOUserAgent = fopFactory.newFOUserAgent();
      // Configurações do FOUserAgente -- basicamente seta as propriedades do PDF
      newFOUserAgent.setTitle("Certidão");
      newFOUserAgent.setAuthor("Equipe Docmanager");
      newFOUserAgent.setSubject("Situação de Processo");
      newFOUserAgent.setCreator("DocManager");
    }
    return newFOUserAgent;
  }

  public byte[] transform(String xml) {
    String fo = xmlToFoTransform(xml);
    return foToPdfTransform(fo);
  }

  private String xmlToFoTransform(String xml) {

    String fo = null;

    if (xml != null) {
      try (StringReader sr = new StringReader(xml); StringWriter sw = new StringWriter();) {
        // Faz a conversão de XML para XSL:FO
        if (this.xmlToFoTransformer != null) {

          StreamSource xmlSource = new StreamSource(sr);
          StreamResult foResult = new StreamResult(sw);
          this.xmlToFoTransformer.transform(xmlSource, foResult);
          // Pega a string gerada
          fo = sw.toString();
        }
      } catch (Exception e) {
        LOGGER.error(e.getMessage(), e);
      }
    }

    return fo;
  }

  private byte[] foToPdfTransform(String fo) {

    byte[] pdfData;

    try (StringReader sourceReader = new StringReader(fo);
        ByteArrayOutputStream resultStream = new ByteArrayOutputStream();

    ) {
      Fop fop = fopFactory.newFop(MimeConstants.MIME_PDF, this.foUserAgent, resultStream);

      // Configura um transformador utilizando as configurações padrão
      TransformerFactory factory = TransformerFactory.newInstance();
      Transformer transformer = factory.newTransformer();

      StreamSource src = new StreamSource(sourceReader);
      // O resultado é processaso pelo FOP para geração do PDF
      SAXResult res = new SAXResult(fop.getDefaultHandler());

      // Executa a transformação
      transformer.transform(src, res);

      InputStream auxStream = new ByteArrayInputStream(resultStream.toByteArray());

      pdfData = IOUtils.toByteArray(auxStream);

    } catch (FOPException | TransformerException | IOException e) {
      LOGGER.error(e.getMessage(), e);
      pdfData = new byte[0];
    }
    return pdfData;
  }
}
