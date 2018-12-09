package business.model;

import java.util.List;

/**
 * Representação de uma Situação em um processo.
 */
public interface Situation {

  //@ model instance nullable String sitDescription;

  //@ ensures \result == null || \result.equals(sitDescription);
  public /*@ pure @*/ String getDescription();

  //@ ensures \result >= 0;
  public /*@ pure @*/ int getId();

  /**
   * Consultar as situações possíveis de acordo com a situação atual.
   * 
   * @return Uma lista de inteiros referente as possíveis situações que poderão ser escolhidas a
   *         partir da atual situação.
   */
  /*@ ensures \result != null && \result.isEmpty() == false;
   @  ensures (\forall int i;
   @               0 <= i && i < \result.size();
   @               \result.get(i) != null && !((Situation)\result.get(i)).getDescription().isEmpty());
   @  ensures (\exists int i;
   @              0 <= i && i < \result.size();
   @              \result.get(i) == this);
   @*/
  public /*@ pure @*/ List<Situation> getlinkedNodes();
}
