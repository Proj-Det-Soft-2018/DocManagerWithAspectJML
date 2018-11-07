package purchase.presentation;

import java.net.URL;
import java.util.Objects;

import org.apache.log4j.Logger;

import business.model.Search;
import business.service.ListService;
import business.service.ProcessService;
import health.presentation.widget.MaskedTextField;
import javafx.beans.property.ReadOnlyStringWrapper;
import javafx.collections.ObservableList;
import javafx.fxml.FXML;
import javafx.scene.control.CheckBox;
import javafx.scene.control.ChoiceBox;
import javafx.scene.control.RadioButton;
import javafx.scene.control.TableColumn;
import javafx.scene.control.TextField;
import javafx.scene.control.ToggleGroup;
import javafx.scene.layout.VBox;
import presentation.ControllerFactory;
import presentation.SearchScreenCtrl;
import presentation.utils.DateUtil;
import purchase.model.PurchaseInterested;
import purchase.model.PurchaseProcess;
import purchase.model.PurchaseProcessSearch;

public class PurchaseSearchScreenCtrl extends SearchScreenCtrl {

	private static final URL FXML_PATH = PurchaseSearchScreenCtrl.class.getResource("/visions/purchase_process_search_screen.fxml");
	private static final Logger LOGGER = Logger.getLogger(PurchaseSearchScreenCtrl.class);

	private ListService listService;

	private MaskedTextField mTxtCnpj;

	@FXML
	private VBox vbInterested;

	@FXML
	private CheckBox checkNumber;

	@FXML
	private CheckBox checkInterested;

	@FXML
	private CheckBox checkOriginEntity;

	@FXML
	private CheckBox checkType;

	@FXML
	private CheckBox checkSituation;

	@FXML
	private ToggleGroup tgBusinessNameCnpj;

	@FXML
	private RadioButton radioBusinessName;

	@FXML
	private RadioButton radioCnpj;

	@FXML
	private MaskedTextField mTxtNumber;

	@FXML
	private TextField txtBusinessName;

	@FXML
	private ChoiceBox<String> choiceOriginEntity;

	@FXML
	private ChoiceBox<String> choiceType;

	@FXML
	private ChoiceBox<String> choiceSituation;

	@FXML
	private TableColumn<PurchaseProcess, String> tabColNumber;

	@FXML
	private TableColumn<PurchaseProcess, String> tabColOriginEntity;

	@FXML
	private TableColumn<PurchaseProcess, String> tabColCnpj;

	@FXML
	private TableColumn<PurchaseProcess, String> tabColSituation;

	@FXML
	private TableColumn<PurchaseProcess, String> tabColRegDate;

	public PurchaseSearchScreenCtrl(ProcessService processService, ListService listService,
			ControllerFactory controllerFactory) {
		super(controllerFactory, processService, LOGGER);
		this.listService = listService;

		// Inicializa o campo de número de CNPJ
		mTxtCnpj = new MaskedTextField("##.###.###/####-##");
		mTxtCnpj.setMaxWidth(520.0);
	}

	@FXML
	private void limparFormulario() {
		checkNumber.setSelected(false);
		checkInterested.setSelected(false);
		checkOriginEntity.setSelected(false);
		checkType.setSelected(false);
		checkSituation.setSelected(false);
		radioBusinessName.setSelected(true);
		choiceOriginEntity.getSelectionModel().select(0);
		choiceType.getSelectionModel().select(0);
		choiceSituation.getSelectionModel().select(0);
		txtBusinessName.clear();
		mTxtNumber.clear();
		mTxtCnpj.clear();
	}

	@Override
	protected void configureForm() {
		fillChoiceBoxes();
		configRadioButton();
		configChoiceBoxOriginEntity();
		configChoiceBoxType();
		configChoiceBoxSituation();
		configTextFieldNumber();
		configTextFieldsInterested();
	}

	private void fillChoiceBoxes() {
		ObservableList<String> obsListaOrgaos = choiceOriginEntity.getItems();
		obsListaOrgaos.addAll(listService.getOrganizationsList());
		choiceOriginEntity.getSelectionModel().select(0);

		ObservableList<String> obsListaAssuntos = choiceType.getItems();
		obsListaAssuntos.addAll(listService.getSubjectsDescritionList());
		choiceType.getSelectionModel().select(0);

		ObservableList<String> obsListaSituacoes = choiceSituation.getItems();
		obsListaSituacoes.addAll(listService.getSituationsDescritionList());
		choiceSituation.getSelectionModel().select(0);
	}

	private void configRadioButton() {
		this.tgBusinessNameCnpj.selectedToggleProperty().addListener(
				(observavel, valorAnterior, novoValor) -> {
					if(Objects.equals(novoValor, radioBusinessName)) {
						vbInterested.getChildren().remove(mTxtCnpj);
						vbInterested.getChildren().add(txtBusinessName);
					} else {
						vbInterested.getChildren().remove(txtBusinessName);
						vbInterested.getChildren().add(mTxtCnpj);
					}
				});
	}

	private void configChoiceBoxOriginEntity() {
		choiceOriginEntity.getSelectionModel().selectedIndexProperty().addListener(
				(observableValue, oldValue, newValue) -> { 
					if (newValue.intValue() != 0) {
						checkOriginEntity.setSelected(true);
					}
				});
	}

	private void configChoiceBoxType() {
		choiceType.getSelectionModel().selectedIndexProperty().addListener(
				(observableValue, oldValue, newValue) -> {
					if (newValue.intValue() != 0)
						checkType.setSelected(true);
				});
	}

	private void configChoiceBoxSituation() {
		choiceSituation.getSelectionModel().selectedIndexProperty().addListener(
				(observableValue, oldValue, newValue) -> {
					if (newValue.intValue() != 0)
						checkSituation.setSelected(true);
				});
	}

	private void configTextFieldNumber() {
		mTxtNumber.focusedProperty().addListener(
				(observableValue, oldValue, newValue) -> {
					if (!newValue && !mTxtNumber.getPlainText().isEmpty()) {
						checkNumber.setSelected(true);
					}
				});
	}

	private void configTextFieldsInterested() {
		txtBusinessName.focusedProperty().addListener(
				(observableValue, oldValue, newValue) -> {
					if (!newValue && !txtBusinessName.getText().isEmpty())
						checkInterested.setSelected(true);
				});
		mTxtCnpj.focusedProperty().addListener(
				(observableValue, oldValue, newValue) -> {
					if (!newValue && !mTxtCnpj.getPlainText().isEmpty())
						checkInterested.setSelected(true);
				});
	}

	@Override
	protected Search mountSearch() {
        String number = (checkNumber.isSelected())? mTxtNumber.getPlainText() : "";
        String businessName = (checkInterested.isSelected() && radioBusinessName.isSelected())? txtBusinessName.getText() : "";
        String cnpj = (checkInterested.isSelected() && radioCnpj.isSelected())? mTxtCnpj.getPlainText() : "";
        int idOriginEntity = checkOriginEntity.isSelected()? choiceOriginEntity.getSelectionModel().getSelectedIndex() : 0;
        int idType = checkType.isSelected()? choiceType.getSelectionModel().getSelectedIndex() : 0;
        int idSituation = checkSituation.isSelected()? choiceSituation.getSelectionModel().getSelectedIndex() : 0;
        
        PurchaseProcessSearch search = new PurchaseProcessSearch();
        search.setNumber(number);
        search.setBusinessName(businessName);
        search.setCnpj(cnpj);
        search.setOrganizationId(idOriginEntity);
        search.setSubjectId(idType);
        search.setSituationId(idSituation);
        
        return search;
    }

	@Override
	protected void configureColumns() {
		tabColNumber.setCellValueFactory(
				content -> new ReadOnlyStringWrapper(content.getValue().getFormattedNumber()));
		tabColOriginEntity.setCellValueFactory(
				content -> new ReadOnlyStringWrapper(content.getValue().getOriginEntityString()));
		tabColCnpj.setCellValueFactory(
				content -> new ReadOnlyStringWrapper(((PurchaseInterested)content.getValue().getInterested()).getFormatedCnpj()));
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
