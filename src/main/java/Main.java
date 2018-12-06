

import business.model.HealthOrganization;
import business.model.HealthSituation;
import business.model.HealthSubject;
import business.service.InterestedServiceImpl;
import business.service.ConcreteListService;
import business.service.ConcreteProcessService;
import business.service.ConcreteStatisticService;
import business.service.InterestedService;
import business.service.ListService;
import business.service.ProcessService;
import business.service.StatisticService;
import business.service.XmlToPdfAdapter;
import business.service.XmlToPdfAdapterImpl;
import javafx.application.Application;
import javafx.stage.Stage;
import persistence.DaoFactory;
import persistence.DaoFactoryJDBC;
import presentation.ControllerFactory;
import presentation.HealthControllerFactory;
import presentation.MainScreenCtrl;


/**
 * @author hugotho
 * 
 */
public class Main extends Application {

  //@ public invariant i >= 0;
  //@ public invariant i >= j;
  static public int i = 0;
  static public int j = 0;

  public static void main(String[] args) {
    launch(args);
  }

  @Override
  public void start(Stage primaryStage) {
    
    i = -1;

    DaoFactory daoFactory = new DaoFactoryJDBC(); 
    XmlToPdfAdapter xmlToPdfAdapter = new XmlToPdfAdapterImpl();
    ProcessService processService = new ConcreteProcessService(daoFactory, xmlToPdfAdapter);
    InterestedService interestedService = new InterestedServiceImpl(daoFactory);
    StatisticService statisticService = new ConcreteStatisticService(daoFactory);

    ListService listService = new ConcreteListService(
        HealthOrganization.getAll(),
        HealthSubject.getAll(),
        HealthSituation.getAll());

    ControllerFactory controllerFactory = new HealthControllerFactory(
        processService,
        interestedService,
        listService,
        statisticService);

    MainScreenCtrl.showMainScreen(primaryStage, controllerFactory.createMainScreenCtrl());
  }
}