/**
 * 
 */
package juridical.presentation;

import java.net.URL;

import org.apache.log4j.Logger;

import business.service.ProcessService;
import javafx.beans.property.ReadOnlyStringWrapper;
import javafx.fxml.FXML;
import javafx.scene.control.TableColumn;
import juridical.model.JuridicalInterested;
import juridical.model.JuridicalProcess;
import presentation.ControllerFactory;
import presentation.MainScreenCtrl;
import presentation.utils.DateUtil;

/**
 * @author clah
 *
 */
public class JuridicalMainScreenCtrl extends MainScreenCtrl {
	
	private static final URL FXML_PATH = JuridicalMainScreenCtrl.class.getResource("/visions/juridical_main_screen.fxml");
	private static final Logger LOGGER = Logger.getLogger(JuridicalMainScreenCtrl.class);
	
	@FXML
	private TableColumn<JuridicalProcess, String> tabColNumber;
	
	@FXML
	private TableColumn<JuridicalProcess, String> tabColInterested;
	
	@FXML
	private TableColumn<JuridicalProcess, String> tabColVara;

	@FXML
	private TableColumn<JuridicalProcess, String> tabColSituation;
	
	@FXML
	private TableColumn<JuridicalProcess, String> tabColRegDate;
	
	protected JuridicalMainScreenCtrl(ProcessService processService, ControllerFactory controllerFactory) {
		super(processService, controllerFactory, LOGGER);
	}

	@Override
	protected void configureColumns() {
		tabColNumber.setCellValueFactory(
				content -> new ReadOnlyStringWrapper(content.getValue().getFormattedNumber()));
		tabColInterested.setCellValueFactory(
				content -> new ReadOnlyStringWrapper(((JuridicalInterested)content.getValue().getInventorian()).getName()));
		tabColVara.setCellValueFactory(
				content -> new ReadOnlyStringWrapper(content.getValue().getCourt().getInitials()));
		tabColSituation.setCellValueFactory(
				content -> new ReadOnlyStringWrapper(content.getValue().getSituation().getDescription()));
		tabColRegDate.setCellValueFactory(
		        content -> new ReadOnlyStringWrapper(DateUtil.format(content.getValue().getRegistrationDate())));
	}

	@Override
	public URL getFxmlPath() {
		return FXML_PATH;
	}

}
