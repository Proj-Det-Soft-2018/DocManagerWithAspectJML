package business.model;

import business.exception.ValidationException;

/**
 * Representação de um Interessado em um Processo.
 */
public interface Interested {

  //@ model instance Long interestedId;

  //@ public invariant interestedId != null && interestedId.longValue() >= 0l;

  //@ ensures \result == interestedId.longValue();
  public /*@ pure @*/ long getId();

  /*@ requires id >= 0l;
   @ assignable interestedId;
   @ ensures interestedId.longValue() == id;
   @*/
  public void setId(long id);

  /**
   * Método que realiza a validação do Interessado.
   * 
   * @throws ValidationException Exceção lançada por problemas de validação do interessado.
   */
  //@ requires this != null;
  public /*@ pure @*/ void validate() throws ValidationException;
}