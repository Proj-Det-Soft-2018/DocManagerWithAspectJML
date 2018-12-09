package business.model;

import java.io.IOException;
import java.io.StringWriter;
import java.time.LocalDateTime;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Marshaller;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;
import javax.xml.bind.annotation.XmlSeeAlso;
import javax.xml.bind.annotation.XmlTransient;

import org.apache.log4j.Logger;

import business.exception.ValidationException;

/**
 * @author lets
 *
 */
@XmlRootElement(name="process")
@XmlSeeAlso(HealthInterested.class)
public class HealthProcess implements Process {

  private static final Logger LOGGER = Logger.getLogger(HealthProcess.class);

  private /*@ spec_public nullable @*/ Long id; //@ in processId;
  //@ protected represents processId <- id;

  private /*@ spec_public nullable @*/ boolean oficio;
  private /*@ spec_public nullable @*/ String number;
  private /*@ spec_public nullable @*/ Interested interested;
  private /*@ spec_public nullable @*/ Subject subject;
  private /*@ spec_public nullable @*/ Organization originEntity;
  private /*@ spec_public nullable @*/ Situation situation;
  private /*@ spec_public nullable @*/ String observation;
  private /*@ spec_public nullable @*/ LocalDateTime registrationDate; //Hora registro do processo no banco
  private /*@ spec_public nullable @*/ LocalDateTime dispatchDate; //Hora que altera e grava situação para concluido

  public HealthProcess() {
    this.id = 0l;
  }

  /*@ assignable id, number, tipoOficio, observation;
	  @ ensures this.id == id && this.oficio == tipoOficio;
	  @	ensures this.number == number && this.observation == observation;
	  @*/
  public HealthProcess(/*@ non_null @*/ Long id, boolean tipoOficio, /*@ non_null @*/ String number,  String observation) {
    this.id = id;
    this.oficio = tipoOficio;
    this.number = number;
    this.observation = observation;
  }

  /*@ assignable id, number, tipoOficio, observation, interested, originEntity, subject, situation;
	  @ ensures this.interested == interested && this.oficio == tipoOficio;
	  @	ensures this.number == number && this.observation == observation;
	  @ ensures this.originEntity == originEntity && this.subject == subject;
	  @ ensures this.situation == situation;
	  @*/
  public HealthProcess(boolean tipoOficio, /*@ non_null @*/String number, /*@ non_null @*/ Interested interested, 
      /*@ non_null @*/ Organization originEntity, /*@ non_null @*/ Subject subject, /*@ non_null @*/ Situation situation, String observation) {
    this.id = 0l;
    this.oficio = tipoOficio;
    this.number = number;
    this.interested = interested;
    this.originEntity = originEntity;
    this.subject = subject;
    this.situation = situation;
    this.observation = observation;
  }

  @Override
  @XmlTransient
  public long getId() {
    return id.longValue();
  }

  @Override
  public void setId(long processId) {
    this.id = processId;
  }

  @XmlTransient
  public boolean isOficio() {
    return oficio;
  }

  public void setTipoOficio(boolean oficio) {
    this.oficio = oficio;
  }

  @XmlElement(name="type")
  public String getType () {
    return this.oficio? "Ofício" : "Processo";
  }

  @XmlElement(name="number")
  public String getFormattedNumber() {
    if(this.isOficio()) {
      return this.number.replaceAll("(\\d{4})(\\d{4})(\\w)", "$1/$2-$3");
    }
    else {
      return this.number.replaceAll("(\\d{5})(\\d{6})(\\d{4})(\\d{2})", "$1.$2/$3-$4");
    }
  }

  @XmlTransient
  public String getNumber() {
    return number;
  }

  public void setNumber(String number){
    this.number = number;
  }

  @XmlElement(name="interested", type=HealthInterested.class)
  public Interested getIntersted() {
    return interested;
  }

  public void setInterested(Interested interested) {
    this.interested = interested;
  }


  @XmlElement(name="subject")
  public String getSubjectString() {
    return subject.getDescription();
  }

  public Subject getSubject() {
    return subject;
  }

  public void setSubjectById(int subjectId){
    this.subject = HealthSubject.getSubjectById(subjectId);
  }

  @XmlElement(name="origin-entity")
  public String getOriginEntityString(){
    return originEntity.getFullName();
  }

  public Organization getOriginEntity() {
    return originEntity;
  }

  public void setOriginEntityById(int originEntityId){
    this.originEntity = HealthOrganization.getOrganizationById(originEntityId);
  }

  @XmlElement(name="situation")
  public String getSituationString() {
    return situation.getDescription();
  }

  public Situation getSituation() {
    return situation;
  }

  public void setSituationById(int situationId){
    this.situation = HealthSituation.getSituationById(situationId);
  }

  @XmlElement(name="observation")
  public String getObservation() {
    return observation;
  }

  @XmlElement(name="entry-date")
  public LocalDateTime getRegistrationDate() {
    return registrationDate;
  }

  public void setRegistrationDate(LocalDateTime registrationDate) {
    this.registrationDate = registrationDate;
  }

  @XmlElement(name="out")
  public LocalDateTime getDispatchDate() {
    return dispatchDate;
  }

  /*@	public normal_behavior
   @		requires dispatchDate.isAfter(this.registrationDate);
   @		assignable this.dispatchDate;
   @		ensures this.dispatchDate == dispatchDate;
   @ also
	 @	public exceptional_behavior
	 @		requires !dispatchDate.isAfter(this.registrationDate);
   @		assignable this.dispatchDate;
   @		signals_only ValidationException;
	 @*/
  public void setDispatchDate(LocalDateTime dispatchDate) throws ValidationException {
    if(dispatchDate.isAfter(this.registrationDate)) {
      this.dispatchDate = dispatchDate;
    }
    else {
      throw new ValidationException("Verifique a Data e a Hora do seu computador.");
    }
  }

  @Override
  public String toXml() {

    StringWriter stringWriter = new StringWriter();
    String xml = null;

    try {
      // Conversão do Objeto para um XML
      JAXBContext jaxbContext = JAXBContext.newInstance(this.getClass());
      Marshaller jaxbMarshaller = jaxbContext.createMarshaller();
      jaxbMarshaller.setProperty(Marshaller.JAXB_FORMATTED_OUTPUT, false);
      jaxbMarshaller.marshal(this, stringWriter);

      xml = stringWriter.toString();
    } catch (JAXBException e) {
      // TODO Mandar uma exception para o controller
      //ExceptionAlert.show("Não foi possível converter o objeto para XML!");
      LOGGER.error(e.getMessage(), e);
    } finally {
      // Fecha o reader e o writer
      try {
        stringWriter.close();
      } catch (IOException e) {
        // TODO Mandar uma exception para o controller
        //ExceptionAlert.show("Não foi possível encerrar os processos!");
        LOGGER.fatal(e.getMessage(), e);
      }
    }
    return xml;
  }

  /*@ also
  @	public normal_behavior
  @   	requires this.oficio;
  @ 		ensures number.length() >= 8 && number.substring(0, 7).matches("[0-9]+");
  @ also
  @	public exceptional_behavior
  @   	requires this.oficio && (number.length() < 8 || !number.substring(0, 7).matches("[0-9]+"));
  @		signals_only ValidationException;
  @ also
  @   requires !this.oficio;
  @   ensures number.length() == 17 && number.matches("[0-9]+");
  @ also
  @	public exceptional_behavior
  @   	requires !this.oficio && (number.length() != 17 || !number.matches("[0-9]+"));
  @		signals_only ValidationException;
  @ also
  @	public normal_behavior
  @   	ensures this.interested != null && this.originEntity != HealthOrganization.NULL;
  @   	ensures this.subject != HealthSubject.NULL && this.situation != HealthSituation.NULL;
  @ also
  @   public exceptional_behavior
	@		requires this.interested == null || this.originEntity == HealthOrganization.NULL;
	@   	requires this.subject == HealthSubject.NULL || this.situation == HealthSituation.NULL;
	@   	requires number.length() != 17 && number.matches("[0-9]+");
	@		signals_only ValidationException;
	@*/
  @Override
  public void validate() throws ValidationException {

    StringBuilder failureMsg = new StringBuilder();
    boolean failure = false;

    if(this.oficio == true) {
      if(number.length() < 8) {
        failure = true;
        failureMsg.append("O número digitado é inválido.\n\n");
      }
      else {
        if(!number.substring(0, 7).matches("[0-9]+")) {
          failure = true;
          failureMsg.append("O número digitado é inválido.\n\n");
        }
      }
    }
    else {
      if(!(number.length() == 17) || !(number.matches("[0-9]+"))) {
        failure = true;
        failureMsg.append("O número digitado é inválido.\n\n");
      }
    }

    if (this.interested == null) {
      failure = true;
      failureMsg.append("O campo Interessado é obrigatório.\n\n");
    }

    if(this.originEntity == HealthOrganization.NULL) {
      failure = true;
      failureMsg.append("O campo Orgão é obrigatório.\n\n");
    }

    if(this.subject == HealthSubject.NULL) {
      failure = true;
      failureMsg.append("Campo assunto é obrigatório.\n\n");
    }

    if(this.situation == HealthSituation.NULL) {
      failure = true;
      failureMsg.append("O campo Situação é obrigatório.\n\n");
    }

    if(failure) {
      failureMsg.delete(failureMsg.length() - 2, failureMsg.length());
      throw new ValidationException(failureMsg.toString());
    }
  }
}
