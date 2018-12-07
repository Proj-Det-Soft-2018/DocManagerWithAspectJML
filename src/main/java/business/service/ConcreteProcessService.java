package business.service;

import business.exception.ValidationException;
import business.model.Process;
import business.model.Search;
import java.io.StringReader;
import java.io.StringWriter;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.util.List;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import org.apache.log4j.Logger;
import org.apache.shiro.SecurityUtils;
import org.apache.shiro.authc.UsernamePasswordToken;
import org.apache.shiro.mgt.DefaultSecurityManager;
import org.apache.shiro.mgt.SecurityManager;
import org.apache.shiro.realm.text.IniRealm;
import org.apache.shiro.subject.Subject;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Text;
import org.xml.sax.InputSource;
import persistence.DaoFactory;
import persistence.ProcessDao;
import persistence.exception.DatabaseException;

/**
 * Classe que concretiza a interface ProcessService, responsável por gerenciar serviços referente
 * aos processos.
 * 
 * @author clarissa - clahzita@gmail.com
 * @since 24/03/2018
 */
public class ConcreteProcessService extends Observable implements ProcessService {

  private static final /*@ spec_public nullable @*/ Logger LOGGER = Logger.getLogger(ConcreteProcessService.class);
  private /*@ spec_public nullable @*/ ProcessDao processoDao;
  private /*@ spec_public nullable @*/ Subject currentUser;
  //private /*@ spec_public nullable @*/ XmlToPdfAdapter xmlToPdfAdapter;

  public ConcreteProcessService(DaoFactory daoFactory/*, XmlToPdfAdapter xmlToPdfAdapter*/) {
    processoDao = daoFactory.getProcessDao();
    //this.xmlToPdfAdapter = xmlToPdfAdapter;

    // Inicilização do Apache Shiro -- utiliza o resources/shiro.ini
    IniRealm iniRealm = new IniRealm("classpath:shiro.ini");
    SecurityManager secutiryManager = new DefaultSecurityManager(iniRealm);
    SecurityUtils.setSecurityManager(secutiryManager);
    currentUser = SecurityUtils.getSubject();
  }

  @Override
  public void save(Process process) throws ValidationException, DatabaseException {
    process.validate();
    processoDao.save(process);
    this.notifyObservers();
  }

  @Override
  public void update(Process process) throws ValidationException, DatabaseException {
    process.validate();
    processoDao.update(process);
    this.notifyObservers();
  }

  @Override
  public void delete(Process process, String admUser, String password) throws DatabaseException {

    if (!this.currentUser.isAuthenticated()) {
      UsernamePasswordToken token = new UsernamePasswordToken(admUser, password);
      token.setRememberMe(true);

      currentUser.login(token); // Joga uma AuthenticationException
    }

    if (currentUser.hasRole("admin")) {
    //if (admUser == "admin" && password == "admin") {
      processoDao.delete(process);
      this.notifyObservers();
    }

    //currentUser.logout();
  }

  @Override
  public List<Process> searchAll(Search searchData) throws ValidationException, DatabaseException {
    searchData.validate();
    return processoDao.searchAll(searchData);
  }

  @Override
  public List<Process> pullList() throws DatabaseException {
    return processoDao.getAllProcessesByPriority();
  }
/*
  @Override
  public byte[] getPdf(Process process) {
    String xml = process.toXml();
    String timedXml = appendCurrentTimeToXml(xml);
    return xmlToPdfAdapter.transform(timedXml);
  }

  private String appendCurrentTimeToXml(String xml) {

    String newXml;

    try (StringReader xmlReader = new StringReader(xml);
        StringWriter xmlWriter = new StringWriter();) {

      // Transforma o String em Document
      DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
      DocumentBuilder db = dbf.newDocumentBuilder();
      InputSource inputSource = new InputSource();
      inputSource.setCharacterStream(xmlReader);
      Document xmlDoc = db.parse(inputSource);

      // Pega o tempo atual e gera uma string formatada
      LocalDateTime now = LocalDateTime.now();
      DateTimeFormatter formatter = DateTimeFormatter.ofPattern("dd/MM/yy HH:mm");
      String formatedTime = now.format(formatter);

      // Cria um novo Elemento com o Texto desejado
      Text text = xmlDoc.createTextNode(formatedTime);
      Element element = xmlDoc.createElement("current-time");
      element.appendChild(text);

      // Coloca o novo elemento no XML
      xmlDoc.getChildNodes().item(0).appendChild(element);

      // Converte de Documento para String
      TransformerFactory tf = TransformerFactory.newInstance();
      Transformer transformer = tf.newTransformer();
      transformer.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "no");
      transformer.setOutputProperty(OutputKeys.METHOD, "xml");
      transformer.setOutputProperty(OutputKeys.INDENT, "yes");
      transformer.setOutputProperty(OutputKeys.ENCODING, "UTF-8");
      transformer.transform(new DOMSource(xmlDoc), new StreamResult(xmlWriter));

      newXml = xmlWriter.toString();

    } catch (Exception e) {
      LOGGER.error(e.getMessage(), e);
      newXml = null;
    }
    return newXml;
  }
*/
}
