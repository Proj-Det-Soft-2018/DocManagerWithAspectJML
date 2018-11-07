package purchase.model;

import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;
import javax.xml.bind.annotation.XmlTransient;

import business.exception.ValidationException;
import business.model.Interested;

@XmlRootElement(name="interested")
public class PurchaseInterested implements Interested {
	private Long id;
	private String cnpj;
	private String businessName;
	private String liableCpf;
	private String liableName;
	private String contact;

	@Override
	@XmlTransient
	public Long getId() {
		return id;
	}

	@Override
	public void setId(Long id) {
		this.id = id;
	}

	@XmlTransient
	public String getCnpj() {
		return cnpj;
	}

	@XmlElement(name="cnpj")
	public String getFormatedCnpj() {
		return cnpj.replaceAll("(\\d{2})(\\d{3})(\\d{3})(\\d{4})(\\d{2})", "$1.$2.$3/$4-$5");
	}

	public void setCnpj(String cnpj) {
		this.cnpj = cnpj;
	}

	@XmlElement(name="business-name")
	public String getBusinessName() {
		return businessName;
	}

	public void setBusinessName(String businessName) {
		this.businessName = businessName;
	}

	@XmlTransient
	public String getLiableCpf() {
		return liableCpf;
	}

	@XmlElement(name="liable-cpf")
	public String getFormatedLiableCpf() {
		return liableCpf.replaceAll("(\\d{3})(\\d{3})(\\d{3})(\\d{2})", "$1.$2.$3-$4");
	}

	public void setLiableCpf(String liableCpf) {
		this.liableCpf = liableCpf;
	}

	@XmlElement(name="liable-name")
	public String getLiableName() {
		return liableName;
	}

	public void setLiableName(String liableName) {
		this.liableName = liableName;
	}

	@XmlTransient
	public String getContact() {
		return contact;
	}

	@XmlElement(name="contact")
	public String getFormatedContact() {
		return contact.replaceAll("(\\d{2})(\\d{5}|\\d{4})(\\d{4})", "($1) $2-$3");
	}

	public void setContact(String contact) {
		this.contact = contact;
	}

	@Override
	public void validate() throws ValidationException {
		StringBuilder failureMsg = new StringBuilder();
		boolean failure = false;
		
		if(this.businessName == null || this.businessName.isEmpty()) {
			failure = true;
			failureMsg.append("O campo Razão Social não pode ser vazio.\n\n");
		}
		else if(!this.businessName.matches("[a-zA-Z\\s]+")) {
			failure = true;
			failureMsg.append("O campo Razão Social deve conter apenas letras.\n\n");
		}
		
		if(liableCpf == null || liableCpf.length() != 11) {
            throw new ValidationException("O campo cpf do responsável não pode ser vazio.\n\n");
        }
		
		if(this.liableName == null || this.liableName.isEmpty()) {
			failure = true;
			failureMsg.append("O campo Nome do Responsável não pode ser vazio.\n\n");
		}
		else if(!this.liableName.matches("[a-zA-Z\\s]+")) {
			failure = true;
			failureMsg.append("O campo Nome do Responsável deve conter apenas letras.\n\n");
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
