package purchase.model;

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

@XmlRootElement(name="process")
@XmlSeeAlso(PurchaseInterested.class)
public class PurchaseProcess implements Process {

	private static final Logger LOGGER = Logger.getLogger(PurchaseInterested.class);

	private Long id;
	private String number;
	private String description;
	private Interested interested;
	private Subject subject;
	private Organization originEntity;
	private Situation situation;
	private String observation;
	private LocalDateTime registrationDate; //Hora registro do processo no banco

	@Override
	@XmlTransient
	public Long getId() {
		return id;
	}

	@Override
	public void setId(Long processId) {
		this.id = processId;
	}

	@XmlTransient
	public String getNumber() {
		return number;
	}

	@XmlElement(name="number")
	public String getFormattedNumber() {
		return this.number.replaceAll("(\\d{5})(\\d{6})(\\d{4})(\\d{2})", "$1.$2/$3-$4");
	}

	public void setNumber(String number) {
		this.number = number;
	}

	public String getDescription() {
		return description;
	}

	public void setDescription(String description) {
		this.description = description;
	}

	@XmlElement(name="interested", type=PurchaseInterested.class)
	public Interested getInterested() {
		return interested;
	}

	public void setInterested(Interested interested) {
		this.interested = interested;
	}

	public Subject getSubject() {
		return subject;
	}

	@XmlElement(name="subject")
	public String getSubjectString() {
		return subject.getDescription();
	}

	public void setSubjectById(int subjectId){
		this.subject = PurchaseSubject.getSubjectById(subjectId);
	}


	public Organization getOriginEntity() {
		return originEntity;
	}

	@XmlElement(name="origin-entity")
	public String getOriginEntityString(){
		return originEntity.getFullName();
	}

	public void setOriginEntityById(int originEntityId){
		this.originEntity = PurchaseOrganization.getOrganizationById(originEntityId);
	}

	public Situation getSituation() {
		return situation;
	}

	@XmlElement(name="situation")
	public String getSituationString() {
		return situation.getDescription();
	}

	public void setSituationById(int situationId){
		this.situation = PurchaseSituation.getSituationById(situationId);
	}

	public String getObservation() {
		return observation;
	}

	public void setObservation(String observation) {
		this.observation = observation;
	}

	@XmlElement(name="entry-date")
	public LocalDateTime getRegistrationDate() {
		return registrationDate;
	}

	public void setRegistrationDate(LocalDateTime registrationDate) {
		this.registrationDate = registrationDate;
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
			LOGGER.error(e.getMessage(), e);
		} finally {
			// Fecha o reader e o writer
			try {
				stringWriter.close();
			} catch (IOException e) {
				// TODO Mandar uma exception para o controller
				LOGGER.fatal(e.getMessage(), e);
			}
		}
		return xml;
	}

	@Override
	public void validate() throws ValidationException {
		StringBuilder failureMsg = new StringBuilder();
		boolean failure = false;

		if( number.length() != 17 || !(number.matches("[0-9]+"))) {
				failure = true;
				failureMsg.append("O número digitado é inválido.\n\n");
		}
		
		if (description == null || description.isEmpty()) {
			failure = true;
			failureMsg.append("O campo Descrição é obrigatório.\n\n");
		}
		
		if (this.interested == null) {
			failure = true;
			failureMsg.append("O campo Interessado é obrigatório.\n\n");
		}

		if(this.originEntity == PurchaseOrganization.NULL) {
			failure = true;
			failureMsg.append("O campo Unidade de Origem é obrigatório.\n\n");
		}

		if(this.subject == PurchaseSubject.NULL) {
			failure = true;
			failureMsg.append("Campo Tipo de Material é obrigatório.\n\n");
		}

		if(this.situation == PurchaseSituation.NULL) {
			failure = true;
			failureMsg.append("O campo Situação é obrigatório.\n\n");
		}

		if(failure) {
			failureMsg.delete(failureMsg.length() - 2, failureMsg.length());
			throw new ValidationException(failureMsg.toString());
		}

	}

}
