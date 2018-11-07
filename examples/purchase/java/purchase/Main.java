package purchase;

import business.service.ConcreteInterestedService;
import business.service.ConcreteListService;
import business.service.ConcreteProcessService;
import business.service.ConcreteStatisticService;
import business.service.InterestedService;
import business.service.ListService;
import business.service.ProcessService;
import business.service.StatisticService;
import business.service.XmlToPdfAdapter;
import business.service.XmlToPdfConcreteAdapter;
import javafx.application.Application;
import javafx.stage.Stage;
import persistence.DaoFactory;
import presentation.ControllerFactory;
import presentation.MainScreenCtrl;
import purchase.model.PurchaseOrganization;
import purchase.model.PurchaseSituation;
import purchase.model.PurchaseSubject;
import purchase.persistence.DaoFactoryJDBC;
import purchase.presentation.PurchaseControllerFactory;

public class Main extends Application {

	public static void main(String[] args) {
		launch(args);
	}

	@Override
	public void start(Stage primaryStage) {

		DaoFactory daoFactory = new DaoFactoryJDBC(); 
		XmlToPdfAdapter xmlToPdfAdapter = new XmlToPdfConcreteAdapter();
		ProcessService processService = new ConcreteProcessService(daoFactory, xmlToPdfAdapter);
		InterestedService interestedService = new ConcreteInterestedService(daoFactory);
		StatisticService statisticService = new ConcreteStatisticService(daoFactory);

		ListService listService = new ConcreteListService(
				PurchaseOrganization.getAll(),
				PurchaseSubject.getAll(),
				PurchaseSituation.getAll());

		ControllerFactory controllerFactory = new PurchaseControllerFactory(
				processService,
				interestedService,
				listService,
				statisticService);

		MainScreenCtrl.showMainScreen(primaryStage, controllerFactory.createMainScreenCtrl());
	}
}
