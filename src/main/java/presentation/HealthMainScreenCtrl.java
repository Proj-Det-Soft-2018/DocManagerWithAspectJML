package presentation;

import java.net.URL;

import org.apache.log4j.Logger;

import business.model.HealthInterested;
import business.model.HealthProcess;
import business.service.ProcessService;
import javafx.beans.property.ReadOnlyStringWrapper;
import javafx.fxml.FXML;
import javafx.scene.control.TableColumn;
import presentation.utils.DateUtil;

/**
 * @author hugotho
 * 
 */
public class HealthMainScreenCtrl extends MainScreenCtrl {
	
	private static final /*@ spec_public nullable @*/ URL FXML_PATH = MainScreenCtrl.class.getResource("/visions/health_main_screen.fxml");
	private static final /*@ spec_public nullable @*/ Logger LOGGER = Logger.getLogger(HealthMainScreenCtrl.class);
	
	@FXML
	private /*@ spec_public nullable @*/  TableColumn<HealthProcess, String> tabColumnType;

	@FXML
	private /*@ spec_public nullable @*/  TableColumn<HealthProcess, String> tabColumnNumber;

	@FXML
	private /*@ spec_public nullable @*/  TableColumn<HealthProcess, String> tabColumnInterested;

	@FXML
	private /*@ spec_public nullable @*/ TableColumn<HealthProcess, String> tabColumnSituation;
	
	@FXML
	private /*@ spec_public nullable @*/  TableColumn<HealthProcess, String> tabColumnRegDate;

	public HealthMainScreenCtrl(ProcessService processService, ControllerFactory controllerFactory) {
		super(processService, controllerFactory, LOGGER);
	}
	
	@Override
	protected void configureColumns() {
		tabColumnType.setCellValueFactory(
				content -> new ReadOnlyStringWrapper(content.getValue().getType()));
		tabColumnNumber.setCellValueFactory(
				content -> new ReadOnlyStringWrapper(content.getValue().getFormattedNumber()));
		tabColumnInterested.setCellValueFactory(
				content -> new ReadOnlyStringWrapper(((HealthInterested)content.getValue().getIntersted()).getName()));
		tabColumnSituation.setCellValueFactory(
				content -> new ReadOnlyStringWrapper(content.getValue().getSituation().getDescription()));
		tabColumnRegDate.setCellValueFactory(
		        content -> new ReadOnlyStringWrapper(DateUtil.format(content.getValue().getRegistrationDate())));
	}
	
	@Override
	public URL getFxmlPath() {
		return FXML_PATH;
	}
}
