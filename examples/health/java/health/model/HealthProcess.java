package health.model;

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
import business.model.Interested;
import business.model.Organization;
import business.model.Process;
import business.model.Situation;
import business.model.Subject;

/**
 * @author lets
 *
 */
@XmlRootElement(name="process")
@XmlSeeAlso(HealthInterested.class)
public class HealthProcess implements Process {

	private static final Logger LOGGER = Logger.getLogger(HealthProcess.class);

	private Long id;
	private boolean oficio;
	private String number;
	private Interested interested;
	private Subject subject;
	private Organization originEntity;
	private Situation situation;
	private String observation;
	private LocalDateTime registrationDate; //Hora registro do processo no banco
	private LocalDateTime dispatchDate; //Hora que altera e grava situação para concluido

	public HealthProcess() {

	}

	public HealthProcess(Long id, boolean tipoOficio, String number,  String observation) {
		this.id = id;
		this.oficio = tipoOficio;
		this.number = number;
		this.observation = observation;
	}

	public HealthProcess(boolean tipoOficio, String number, Interested interested, Organization originEntity, Subject subject, Situation situation, String observation) {
		this.oficio = tipoOficio;
		this.number = number;
		this.interested = interested;
		this.originEntity = originEntity;
		this.subject = subject;
		this.situation = situation;
		this.observation = observation;
	}

	/* (non-Javadoc)
	 * @see business.model.Process#getId()
	 */
	@Override
	@XmlTransient
	public Long getId() {
		return id;
	}

	/* (non-Javadoc)
	 * @see business.model.Process#setId(java.lang.Long)
	 */
	@Override
	public void setId(Long processId) {
		this.id = processId;
	}

	/* (non-Javadoc)
	 * @see business.model.Process#isOficio()
	 */
	@XmlTransient
	public boolean isOficio() {
		return oficio;
	}

	/* (non-Javadoc)
	 * @see business.model.Process#setTipoOficio(boolean)
	 */
	public void setTipoOficio(boolean oficio) {
		this.oficio = oficio;
	}

	/* (non-Javadoc)
	 * @see business.model.Process#getType()
	 */
	@XmlElement(name="type")
	public String getType () {
		return this.oficio? "Ofício" : "Processo";
	}

	/* (non-Javadoc)
	 * @see business.model.Process#getFormattedNumber()
	 */
	@XmlElement(name="number")
	public String getFormattedNumber() {
		if(this.isOficio()) {
			return this.number.replaceAll("(\\d{4})(\\d{4})(\\w)", "$1/$2-$3");
		}
		else {
			return this.number.replaceAll("(\\d{5})(\\d{6})(\\d{4})(\\d{2})", "$1.$2/$3-$4");
		}
	}

	/* (non-Javadoc)
	 * @see business.model.Process#getNumber()
	 */
	@XmlTransient
	public String getNumber() {
		return number;
	}

	/* (non-Javadoc)
	 * @see business.model.Process#setNumber(java.lang.String)
	 */
	public void setNumber(String number){
		this.number = number;
	}

	/* (non-Javadoc)
	 * @see business.model.Process#getIntersted()
	 */
	@XmlElement(name="interested", type=HealthInterested.class)
	public Interested getIntersted() {
		return interested;
	}

	/* (non-Javadoc)
	 * @see business.model.Process#setInterested(business.model.HealthInterested)
	 */
	public void setInterested(Interested interested) {
		this.interested = interested;
	}


	/* (non-Javadoc)
	 * @see business.model.Process#getSubjectString()
	 */
	@XmlElement(name="subject")
	public String getSubjectString() {
		return subject.getDescription();
	}

	/* (non-Javadoc)
	 * @see business.model.Process#getSubject()
	 */
	public Subject getSubject() {
		return subject;
	}

	/* (non-Javadoc)
	 * @see business.model.Process#setSubjectById(int)
	 */
	public void setSubjectById(int subjectId){
		this.subject = HealthSubject.getSubjectById(subjectId);
	}

	/* (non-Javadoc)
	 * @see business.model.Process#getOriginEntityString()
	 */
	@XmlElement(name="origin-entity")
	public String getOriginEntityString(){
		return originEntity.getFullName();
	}

	/* (non-Javadoc)
	 * @see business.model.Process#getOriginEntity()
	 */
	public Organization getOriginEntity() {
		return originEntity;
	}

	/* (non-Javadoc)
	 * @see business.model.Process#setOriginEntityById(int)
	 */
	public void setOriginEntityById(int originEntityId){
		this.originEntity = HealthOrganization.getOrganizationById(originEntityId);
	}

	/* (non-Javadoc)
	 * @see business.model.Process#getSituationString()
	 */
	@XmlElement(name="situation")
	public String getSituationString() {
		return situation.getDescription();
	}

	/* (non-Javadoc)
	 * @see business.model.Process#getSituation()
	 */
	public Situation getSituation() {
		return situation;
	}

	/* (non-Javadoc)
	 * @see business.model.Process#setSituationById(int)
	 */
	public void setSituationById(int situationId){
		this.situation = HealthSituation.getSituationById(situationId);
	}

	/* (non-Javadoc)
	 * @see business.model.Process#getObservation()
	 */
	@XmlElement(name="observation")
	public String getObservation() {
		return observation;
	}

	/* (non-Javadoc)
	 * @see business.model.Process#getRegistrationDate()
	 */
	@XmlElement(name="entry-date")
	public LocalDateTime getRegistrationDate() {
		return registrationDate;
	}

	/* (non-Javadoc)
	 * @see business.model.Process#setRegistrationDate(java.time.LocalDateTime)
	 */
	public void setRegistrationDate(LocalDateTime registrationDate) {
		this.registrationDate = registrationDate;
	}

	/* (non-Javadoc)
	 * @see business.model.Process#getDispatchDate()
	 */
	@XmlElement(name="out")
	public LocalDateTime getDispatchDate() {
		return dispatchDate;
	}

	/* (non-Javadoc)
	 * @see business.model.Process#setDispatchDate(java.time.LocalDateTime)
	 */
	public void setDispatchDate(LocalDateTime dispatchDate) throws ValidationException {
		if(dispatchDate.isAfter(this.registrationDate)) {
			this.dispatchDate = dispatchDate;
		}
		else {
			throw new ValidationException("Verifique a Data e a Hora do seu computador.");
		}
	}

	/* (non-Javadoc)
	 * @see business.model.Process#toXml()
	 */
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
