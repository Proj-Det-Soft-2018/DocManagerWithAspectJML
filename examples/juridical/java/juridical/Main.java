package juridical;

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
import juridical.persistence.DaoFactoryJDBC;
import juridical.presentation.JuridicalControllerFactory;
import javafx.application.Application;
import javafx.stage.Stage;
import juridical.model.JuridicalJudge;
import juridical.model.JuridicalOrganization;
import juridical.model.JuridicalSituation;
import persistence.DaoFactory;
import presentation.ControllerFactory;
import presentation.MainScreenCtrl;

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
				JuridicalOrganization.getAll(),
				JuridicalJudge.getAll(),
				JuridicalSituation.getAll());

		ControllerFactory controllerFactory = new JuridicalControllerFactory(
				processService,
				interestedService,
				listService,
				statisticService);

		MainScreenCtrl.showMainScreen(primaryStage, controllerFactory.createMainScreenCtrl());
	}

}
