package business.model;

import java.util.List;

/**
 * Representação de uma Situação em um processo.
 */
public interface Situation {

  String getDescription();

  int getId();

  /**
   * Consultar as situações possíveis de acordo com a situação atual.
   * 
   * @return Uma lista de inteiros referente as possíveis situações que poderão ser escolhidas a
   *         partir da atual situação.
   */
  List<Situation> getlinkedNodes();
}
