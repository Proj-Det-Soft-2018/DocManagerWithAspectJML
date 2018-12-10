package business.model;

/**
 * Representação de um Assunto de um processo.
 */
public interface Subject {

  //@ model instance nullable String subjDescription;
  //@ model instance nullable String subjShortDesc;
  
  //@ ensures \result == null || \result.equals(subjDescription);
  public /*@ pure @*/String getDescription();

  //@ ensures \result == null || \result.equals(subjShortDesc);
  public /*@ pure @*/String getShortDescription();

  //@ ensures \result >= 0;
  public /*@ pure @*/int getId();
}
