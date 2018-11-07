/**
 * 
 */
package health.model;

import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;
import javax.xml.bind.annotation.XmlTransient;

import business.exception.ValidationException;
import business.model.Interested;

/**
 * Classe representa o interessado do processo, pessoa vinculada ao processo como
 * parte interessada.
 * 
 * @author clah
 *
 */
@XmlRootElement(name="interested")
public class HealthInterested implements Interested {
	private Long id;
	private String name;
	private String cpf;
	private String contact;
	
	
	
	public HealthInterested(Long id, String nome, String cpf, String contato) {
		this.id = id;
		this.name = nome;
		this.cpf = cpf;
		this.contact = contato;
	}
	
	public HealthInterested(String nome, String cpf, String contato) {
		this.name = nome;
		this.cpf = cpf;
		this.contact = contato;
	}
	
	public HealthInterested() {}

	/* (non-Javadoc)
	 * @see business.model.Interested#getId()
	 */
	@Override
	@XmlTransient
	public Long getId() {
		return id;
	}

	/* (non-Javadoc)
	 * @see business.model.Interested#setId(java.lang.Long)
	 */
	@Override
	public void setId(Long id) {
		this.id = id;
	}

	/* (non-Javadoc)
	 * @see business.model.Interested#getName()
	 */
	@XmlElement
	public String getName() {
		return name;
	}


	/* (non-Javadoc)
	 * @see business.model.Interested#setName(java.lang.String)
	 */
	public void setName(String name){
		this.name = name;
	}
	
	/* (non-Javadoc)
	 * @see business.model.Interested#getFormatedCpf()
	 */
	@XmlElement(name="cpf")
	public String getFormatedCpf() {
		return cpf.replaceAll("(\\d{3})(\\d{3})(\\d{3})(\\d{2})", "$1.$2.$3-$4");
	}
	
	/* (non-Javadoc)
	 * @see business.model.Interested#getCpf()
	 */
	@XmlTransient
	public String getCpf() {
		return cpf;
	}


	/* (non-Javadoc)
	 * @see business.model.Interested#setCpf(java.lang.String)
	 */
	public void setCpf(String cpf) {
		this.cpf = cpf;
	}
	
	/* (non-Javadoc)
	 * @see business.model.Interested#getFormatedContact()
	 */
	@XmlElement(name="contact")
	public String getFormatedContact() {
		return contact.replaceAll("(\\d{2})(\\d{5}|\\d{4})(\\d{4})", "($1) $2-$3");
	}
	
	/* (non-Javadoc)
	 * @see business.model.Interested#getContact()
	 */
	@XmlTransient
	public String getContact() {
		return contact;
	}
	
	/* (non-Javadoc)
	 * @see business.model.Interested#setContact(java.lang.String)
	 */
	public void setContact(String contact){
		this.contact = contact;
	}

	@Override
	public void validate() throws ValidationException {
		
		StringBuilder failureMsg = new StringBuilder();
		boolean failure = false;
		
		if(this.name == null || this.name.isEmpty()) {
			failure = true;
			failureMsg.append("O campo Nome não pode ser vazio.\n\n");
		}
		else if(!this.name.matches("[a-zA-Z\\s]+")) {
			failure = true;
			failureMsg.append("O campo Nome deve conter apenas letras.\n\n");
		}
		
		if(this.contact == null || (!this.contact.isEmpty() && this.contact.length() < 10)){
			failure = true;
			failureMsg.append("O contato inserido está incompleto.\n\n");
		}
		
		if(failure) {
			failureMsg.delete(failureMsg.length() - 2, failureMsg.length());
			throw new ValidationException(failureMsg.toString());
		}
		
	}
}