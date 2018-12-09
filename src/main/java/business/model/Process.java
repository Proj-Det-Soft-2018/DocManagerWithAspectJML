package business.model;

import business.exception.ValidationException;

/**
 * Representação de um Processo.
 */
public interface Process {
	
  //@ model instance Long processId;

  //@ public invariant processId != null && processId.longValue() >= 0l;
  
  //@ ensures \result == processId.longValue();
	public /*@ pure @*/  long getId();

 /*@ requires id >= 0l;
   @ assignable processId;
   @ ensures processId.longValue() == id;
   @*/
  public void setId(long id);

  /**
   * Transforma o Objeto Processo em um arquivo Xml.
   * 
   * @return Arquivo XML como String
   */
  String toXml();

  /**
   * Realiza a validação da classe Process.
   * 
   * @throws ValidationException Exceção lançada por problemas de validação do processo.
   */
 /*@ requires this != null;
   @*/
  public /*@ pure @*/ void validate() throws ValidationException;

}
