package juridical.model;

import java.io.IOException;
import java.io.StringWriter;
import java.time.LocalDateTime;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Marshaller;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlTransient;

import org.apache.log4j.Logger;

import business.exception.ValidationException;
import business.model.Interested;
import business.model.Organization;
import business.model.Process;
import business.model.Situation;
import business.model.Subject;


public class JuridicalProcess implements Process {
	private static Logger LOGGER = Logger.getLogger(JuridicalProcess.class);

	private Long id;
	private String number;
	private Interested inventorian;
	private Subject judge; //Ta bizarro
	private Organization court;
	private Situation situation;
	private String lawyerName;
	private String inventoriedName;
	private String observation;
	private LocalDateTime registrationDate; //Hora registro do processo no banco
	
	public JuridicalProcess() {	}

	public JuridicalProcess(Long id, String number,  String observation) {
		this.id = id;
		this.number = number;
		this.observation = observation;
	}

	public JuridicalProcess(String number, Interested inventorian, 
			Organization court, Subject judge, Situation situation, 
			String lawyerName, String inventoriedName, String observation) {
		this.number = number;
		this.court = court;
		this.judge = judge;
		this.situation = situation;
		this.lawyerName = lawyerName;
		this.inventoriedName = inventoriedName;
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
	 * @see business.model.Process#getFormattedNumber()
	 */
	@XmlElement(name="number")
	public String getFormattedNumber() {
		return this.number.replaceAll("(\\d{5})(\\d{6})(\\d{4})(\\d{2})", "$1.$2/$3-$4");
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

	/**
	 * @return the inventorian
	 */
	@XmlElement(name="interested", type=JuridicalInterested.class)
	public Interested getInventorian() {
		return inventorian;
	}

	/**
	 * @param inventorian the inventorian to set
	 */
	public void setInventorian(Interested inventorian) {
		this.inventorian = inventorian;
	}

	/**
	 * @return the judge
	 */
	@XmlElement(name="subject")
	public Subject getJudge() {
		return judge;
	}

	/**
	 * @param judge the judge to set
	 */
	public void setJudge(Subject judge) {
		this.judge = judge;
	}
	
	public void setJudgeById(int id) {
		this.judge = JuridicalJudge.getSubjectById(id);
	}


	/**
	 * @return the court
	 */
	@XmlElement(name="origin-entity")
	public Organization getCourt() {
		return court;
	}

	/**
	 * @param court the court to set
	 */
	public void setCourt(Organization court) {
		this.court = court;
	}
	
	public void setCourtById(int id) {
		this.court = JuridicalOrganization.getOrganizationById(id);
	}

	/**
	 * @return the lawyerName
	 */
	public String getLawyerName() {
		return lawyerName;
	}

	/**
	 * @param lawyerName the lawyerName to set
	 */
	public void setLawyerName(String lawyerName) {
		this.lawyerName = lawyerName;
	}

	/**
	 * @return the inventoriedName
	 */
	public String getInventoriedName() {
		return inventoriedName;
	}

	public void setInventoriedName(String inventoriedName) {
		this.inventoriedName = inventoriedName;
	}

	@XmlElement(name="situation")
	public String getSituationString() {
		return situation.getDescription();
	}

	public Situation getSituation() {
		return situation;
	}

	/**
	 * @param situation the situation to set
	 */
	public void setSituation(Situation situation) {
		this.situation = situation;
	}
	
	public void setSituationById(int id) {
		this.situation = JuridicalSituation.getSituationById(id);
	}

	@XmlElement(name="observation")
	public String getObservation() {
		return observation;
	}

	/**
	 * @param observation the observation to set
	 */
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


		if(!(number.length() == 17) || !(number.matches("[0-9]+"))) {
			failure = true;
			failureMsg.append("O número do processo digitado é inválido.\n\n");
		}


		if(this.lawyerName == null || this.lawyerName.isEmpty()) {
			failure = true;
			failureMsg.append("O campo Nome do Advogado não pode ser vazio.\n\n");
		}
		else if(!this.lawyerName.matches("[a-zA-Z\\s]+")) {
			failure = true;
			failureMsg.append("O campo Nome do Advogado deve conter apenas letras.\n\n");
		}

		if(this.inventoriedName == null || this.inventoriedName.isEmpty()) {
			failure = true;
			failureMsg.append("O campo Nome do Inventariado não pode ser vazio.\n\n");
		}
		else if(!this.inventoriedName.matches("[a-zA-Z\\s]+")) {
			failure = true;
			failureMsg.append("O campo Nome do Inventariado deve conter apenas letras.\n\n");
		}



		if(this.court == JuridicalOrganization.NULL) {
			failure = true;
			failureMsg.append("O campo Orgão é obrigatório.\n\n");
		}

		if(this.judge == JuridicalJudge.NULL) {
			failure = true;
			failureMsg.append("Campo juiz é obrigatório.\n\n");
		}

		if(this.situation == JuridicalSituation.NULL) {
			failure = true;
			failureMsg.append("O campo Situação é obrigatório.\n\n");
		}

		if(failure) {
			failureMsg.delete(failureMsg.length() - 2, failureMsg.length());
			throw new ValidationException(failureMsg.toString());
		}
	}


}



