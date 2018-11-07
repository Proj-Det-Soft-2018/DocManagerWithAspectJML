/**
 * 
 */
package juridical.model;

import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlTransient;

import business.exception.ValidationException;
import business.model.Interested;

/**
 * @author clah
 *
 */
public class JuridicalInterested implements Interested {
	private Long id;
	private String name;
	private int idade;
	private String cpf;
	private String contact;
	private String email;
	
	public JuridicalInterested(){}
	
	public JuridicalInterested(Long id, String nome, int idade, String cpf, String contato, String email) {
		this.id = id;
		this.name = nome;
		this.idade = idade;
		this.cpf = cpf;
		this.contact = contato;
		this.email = email;
	}
	
	public JuridicalInterested(String nome, String cpf, String contato, String email) {
		this.name = nome;
		this.cpf = cpf;
		this.contact = contato;
		this.email = email;
	}
	
	/* (non-Javadoc)
	 * @see business.model.Interested#getId()
	 */
	@Override
	public Long getId() {
		return this.id;
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
	
	public int getIdade() {
		return idade;
	}

	public void setIdade(int idade) {
		this.idade = idade;
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
	
	public String getEmail() {
		return email;
	}
	
	public void setEmail(String email) {
		this.email = email;
	}

	/* (non-Javadoc)
	 * @see business.model.Interested#validate()
	 */
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
		
    	//TODO fazer validação do email

		
		if(failure) {
			failureMsg.delete(failureMsg.length() - 2, failureMsg.length());
			throw new ValidationException(failureMsg.toString());
		}

	}

}
