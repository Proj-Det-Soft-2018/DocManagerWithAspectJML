package business.service;

import business.exception.ValidationException;
import business.model.Interested;
import business.model.Search;
import persistence.DaoFactory;
import persistence.InterestedDao;
import persistence.exception.DatabaseException;

/**
 * Classe que concretiza a interface de InterestedService, responsável por gerenciar serviços
 * referente ao interessado do processo.
 * 
 * @author Allan
 *
 */
public class ConcreteInterestedService extends Observable implements InterestedService {

  private InterestedDao interessadoDao;

  /**
   * Constrói uma instância com uma fábrica de DAO que instancia o atributo interessadoDao.
   * 
   * @param daoFactory Fábrica de objetos de controle de banco de dados.
   */
  public ConcreteInterestedService(DaoFactory daoFactory) {
    interessadoDao = daoFactory.getInterestedDao();
  }

  @Override
  public void save(Interested interessado) throws DatabaseException {
    interessadoDao.save(interessado);
    notifyObservers();
  }

  @Override
  public void update(Interested interessado) throws DatabaseException {
    interessadoDao.update(interessado);
    notifyObservers();
  }

  @Override
  public void delete(Interested interessado) throws DatabaseException {
    interessadoDao.delete(interessado);
    notifyObservers();
  }

  @Override
  public Interested search(Search searchData) throws ValidationException, DatabaseException {
    searchData.validate();
    return interessadoDao.search(searchData);
  }
}
