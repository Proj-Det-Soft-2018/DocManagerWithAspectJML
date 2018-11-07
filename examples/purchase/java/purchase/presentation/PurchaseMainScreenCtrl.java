package purchase.presentation;

import java.net.URL;

import org.apache.log4j.Logger;

import business.service.ProcessService;
import javafx.beans.property.ReadOnlyStringWrapper;
import javafx.fxml.FXML;
import javafx.scene.control.TableColumn;
import presentation.ControllerFactory;
import presentation.MainScreenCtrl;
import presentation.utils.DateUtil;
import purchase.model.PurchaseInterested;
import purchase.model.PurchaseProcess;

public class PurchaseMainScreenCtrl extends MainScreenCtrl {
	
	private static final URL FXML_PATH = PurchaseMainScreenCtrl.class.getResource("/visions/purchase_main_screen.fxml");
	private static final Logger LOGGER = Logger.getLogger(PurchaseMainScreenCtrl.class);
	
	@FXML
	private TableColumn<PurchaseProcess, String> tabColumnNumber;
	
	@FXML
	private TableColumn<PurchaseProcess, String> tabColumnOriginEntity;
	
	@FXML
	private TableColumn<PurchaseProcess, String> tabColumnInterestedCnpj;

	@FXML
	private TableColumn<PurchaseProcess, String> tabColumnSituation;
	
	@FXML
	private TableColumn<PurchaseProcess, String> tabColumnRegDate;

	public PurchaseMainScreenCtrl(ProcessService processService, ControllerFactory controllerFactory) {
		super(processService, controllerFactory, LOGGER);
	}
	
	@Override
	protected void configureColumns() {
		tabColumnNumber.setCellValueFactory(
				content -> new ReadOnlyStringWrapper(content.getValue().getFormattedNumber()));
		tabColumnOriginEntity.setCellValueFactory(
				content -> new ReadOnlyStringWrapper(content.getValue().getOriginEntityString()));
		tabColumnInterestedCnpj.setCellValueFactory(
				content -> new ReadOnlyStringWrapper(((PurchaseInterested)content.getValue().getInterested()).getFormatedCnpj()));
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
