package business.model;

/**
 * Representação de uma Organização em um determinado processo.
 */
public interface Organization {
  
  //@ model instance nullable String orgFullName;
 
  //@ ensures \result == null || \result.equals(orgFullName);
  public /*@ pure @*/ String getFullName();

  //@ ensures \result != null;
  public /*@ pure @*/ String getInitials();

  //@ ensures \result >= 0;
  public /*@ pure @*/ int getId();
}
