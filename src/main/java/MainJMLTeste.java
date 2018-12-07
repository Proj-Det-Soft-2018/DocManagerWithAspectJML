import business.exception.ValidationException;
import business.model.HealthInterested;
import business.model.HealthOrganization;
import business.model.HealthProcess;
import business.model.HealthSituation;
import business.model.HealthSubject;
import business.service.ConcreteListService;
import business.service.ConcreteProcessService;
import business.service.ConcreteStatisticService;
import business.service.InterestedService;
import business.service.InterestedServiceImpl;
import business.service.ListService;
import business.service.ProcessService;
import business.service.StatisticService;
import persistence.DaoFactory;
import persistence.DaoFactoryJDBC;
import persistence.exception.DatabaseException;

public class MainJMLTeste {

  public static void main(String[] args) {
    DaoFactory daoFactory = new DaoFactoryJDBC();
    ProcessService processService = new ConcreteProcessService(daoFactory);
    InterestedService interestedService = new InterestedServiceImpl(daoFactory);
    StatisticService statisticService = new ConcreteStatisticService(daoFactory);

    ListService listService = new ConcreteListService(
        HealthOrganization.getAll(),
        HealthSubject.getAll(),
        HealthSituation.getAll());
    
    try {
      System.out.println(((HealthProcess)(processService.pullList().get(0))).getNumber());
    } catch (DatabaseException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
    
  }
}
