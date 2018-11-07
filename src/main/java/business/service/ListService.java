package business.service;

import business.model.Situation;
import java.util.List;

/**
 * Estabelece os métodos para gerenciamento de serviços de listas de organizações, situações e
 * assuntos.
 *
 */
public interface ListService {

  /**
   * Pega a lista de todas organização que o processo pode pertencer.
   * 
   * @return
   */
  List<String> getOrganizationsList();

  /**
   * Pega a sigla da organização pelo número identificador da organização.
   * 
   * @param id número identificador da organização.
   * @return Sigla da organização identificada pelo número passado em id.
   */
  String getOrganizationInitialsById(int id);

  /**
   * Retorna uma lista com todas descrições de cada assunto.
   * 
   * @return retorna uma lista de strings com as descrições de cada assunto.
   */
  List<String> getSubjectsDescritionList();

  /**
   * Pega a descrição curta do assunto por identificador numérico.
   * 
   * @param id idenficador numérico do assunto.
   * @return uma string com a descrição curta do assunto.
   */
  String getSujectShortDescritionById(int id);

  /**
   * Retorna uma lista com todas as descrições das situações do processo.
   * 
   * @return
   */
  List<String> getSituationsDescritionList();

  /**
   * Retorna uma descriçao de uma situação por identificador numérico.
   * 
   * @param id identificador numérico da situação.
   * @return uma string com a descrição da situação.
   */
  String getSituationDescritionById(int id);

  /**
   * Retorna uma lista de situações de acordo com a situação atual.
   * 
   * @param currentSituation situação atual que define que situações serão listadas.
   * @return lista de string com todas as situações que são possiveis de mudar, considerando a
   *         situação atual do processo.
   */
  List<String> getSituationsListByCurrentSituation(Situation currentSituation);

}
