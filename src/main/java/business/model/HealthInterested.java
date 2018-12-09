/**
 * 
 */
package business.model;

import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;
import javax.xml.bind.annotation.XmlTransient;

import business.exception.ValidationException;

/**
 * Classe representa o interessado do processo, pessoa vinculada ao processo como
 * parte interessada.
 * 
 * @author clah
 *
 */
@XmlRootElement(name="interested")
public class HealthInterested implements Interested {
	private /*@ spec_public nullable @*/ Long id;
	private /*@ spec_public nullable @*/ String name;
	private /*@ spec_public nullable @*/ String cpf;
	private /*@ spec_public nullable @*/ String contact;
	
	
	
	/*@ assignable this.id, this.name, this.cpf, this.contact;
	  @ ensures this.id == id && this.name == nome;
	  @	ensures this.cpf == cpf && this.contact == contato;
	  @*/
	public HealthInterested(/*@ non_null @*/Long id, /*@ non_null @*/String nome, /*@ non_null @*/String cpf, /*@ non_null @*/String contato) {
		this.id = id;
		this.name = nome;
		this.cpf = cpf;
		this.contact = contato;
		
	}
	
	/*@ assignable this.name, this.cpf, this.contact;
	  @ ensures this.name == nome;
	  @	ensures this.cpf == cpf && this.contact == contato;
	  @*/
	public HealthInterested(/*@ non_null @*/String nome, /*@ non_null @*/String cpf, /*@ non_null @*/String contato) {
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
	
   /*@ also
     @  public normal_behavior
     @ 		ensures this.contact != null && this.contact.length() > 10; 
     @ 		ensures this.name != null && this.name.length() != 0;
     @ 		ensures this.name.matches("[a-zA-Z\\s]+");
     @ 		ensures this.cpf != null && this.cpf.length() == 11;
     @ also
     @   public exceptional_behavior
     @ 		requires this.contact == null || this.contact.length() <= 10; 
     @ 		requires this.name == null || this.name.length() == 0;
     @ 		requires !this.name.matches("[a-zA-Z\\s]+");
     @ 		requires this.cpf == null || this.cpf.length() != 11;
     @		signals_only ValidationException;	 
	 @*/
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
		
		if(this.cpf == null || (this.cpf.length() != 11)){
			failure = true;
			failureMsg.append("O cpf inserido está incompleto.\n\n");
		}
		
		if(failure) {
			failureMsg.delete(failureMsg.length() - 2, failureMsg.length());
			throw new ValidationException(failureMsg.toString());
		}
		
	}
}