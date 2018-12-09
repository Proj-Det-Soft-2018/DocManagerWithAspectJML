package business.model;

import business.exception.ValidationException;

/**
 * Representação de um Processo.
 */
public interface Process {
	
	/*@ pure @*/  Long getId();

  void setId(Long processId);

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
