package business.service;

import java.util.ArrayList;
import java.util.Map;
import persistence.DaoFactory;
import persistence.ProcessDao;
import persistence.exception.DatabaseException;

/**
 * Classe que concretiza a interface StatisticService, responsável por gerenciar serviços de
 * gráficos estatísticos dos processos.
 * 
 * @author clah
 * @since 04.20.2018
 */
public class ConcreteStatisticService implements StatisticService {

  private /*@ spec_public @*/ ProcessDao processoDao;

  /**
   * Constrói uma instância com uma fábrica de DAO que instancia o atributo processoDao.
   * 
   * @param daoFactory Fábrica de objetos de controle de banco de dados.
   */
/*@ assignable processoDao;
  @ ensures processoDao != null;
  @*/
  public ConcreteStatisticService(DaoFactory daoFactory) {
    processoDao = daoFactory.getProcessDao();
  }

  @Override
  public Map<Integer, ArrayList<Integer>> quantityProcessPerMonthYear() throws DatabaseException {
    return processoDao.getQuantityProcessPerMonthYearList();
  }

  @Override
  public Map<Integer, Integer> quantityProcessPerSituation() throws DatabaseException {
    return processoDao.getQuantityProcessPerSituationList();
  }

  @Override
  public Map<Integer, ArrayList<Integer>> quantityProcessFromLastYear() throws DatabaseException {
    return processoDao.getQuantityProcessPerMonthFromLastYearList();
  }

  @Override
  public Map<Integer, Integer> quantityProcessPerOrganization() throws DatabaseException {
    return processoDao.getQuantityProcessPerOrganizationList();
  }

  @Override
  public Map<Integer, Integer> quantityProcessPerSubject() throws DatabaseException {
    return processoDao.getQuantityProcessPerSubjectList();
  }

}
