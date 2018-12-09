package business.model;

import business.exception.ValidationException;

public class HealthInterestedSearch implements Search {
    
    private /*@ spec_public nullable @*/ String cpf; //@ in cpfInterested;
    /*@ protected represents
    @ cpfInterested = cpf;
    @*/

    /*@ also
    @  public normal_behavior
    @ 		ensures  !(cpf.length() != 11);
    @ also
    @   public exceptional_behavior
    @ 		requires cpf == null || cpf.length() != 11;
    @		signals_only ValidationException;	 
	 @*/
    @Override
    public void validate() throws ValidationException {
        if(cpf == null || cpf.length() != 11) {
            throw new ValidationException("O CPF buscado está incompleto!");
        }
    }

    public String getCpf() {
        return cpf;
    }

    public void setCpf(String cpf) {
        this.cpf = cpf;
    }
}
