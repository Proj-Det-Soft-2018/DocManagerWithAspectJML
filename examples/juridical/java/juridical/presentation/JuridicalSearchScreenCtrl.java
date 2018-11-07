package juridical.presentation;

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
import juridical.model.JuridicalInterested;
import juridical.model.JuridicalProcess;
import juridical.model.JuridicalProcessSearch;
import presentation.ControllerFactory;
import presentation.SearchScreenCtrl;
import presentation.utils.DateUtil;

public class JuridicalSearchScreenCtrl extends SearchScreenCtrl {

	private static final URL FXML_PATH = JuridicalSearchScreenCtrl.class.getResource("/visions/juridical_process_search_screen.fxml");
	private static final Logger LOGGER = Logger.getLogger(JuridicalSearchScreenCtrl.class);

	private ListService listService;

	private MaskedTextField mTxtCpf;

	@FXML
	private VBox vbInteressado;

	@FXML
	private CheckBox checkNumber;

	@FXML
	private CheckBox checkInterested;

	@FXML
	private CheckBox checkInventaried;

	@FXML
	private CheckBox checkLawyer;

	@FXML
	private CheckBox checkCourt;

	@FXML
	private CheckBox checkJudge;

	@FXML
	private CheckBox checkSituation;

	@FXML
	private ToggleGroup tgNomeCpf;

	@FXML
	private RadioButton radioNome;

	@FXML
	private RadioButton radioCpf;

	@FXML
	private MaskedTextField mTxtNumber;

	@FXML
	private TextField txtName;

	@FXML
	private TextField txtInventaried;

	@FXML
	private TextField txtLawyer;

	@FXML
	private ChoiceBox<String> cbCourt;

	@FXML
	private ChoiceBox<String> cbJudge;

	@FXML
	private ChoiceBox<String> cbSituation;

	@FXML
	private TableColumn<JuridicalProcess, String> tabColNumber;

	@FXML
	private TableColumn<JuridicalProcess, String> tabColInterested;

	@FXML
	private TableColumn<JuridicalProcess, String> tabColCourt;

	@FXML
	private TableColumn<JuridicalProcess, String> tabColSituation;

	@FXML
	private TableColumn<JuridicalProcess, String> tabColRegDate;


	public JuridicalSearchScreenCtrl(ProcessService processService, ListService listService,
			ControllerFactory controllerFactory) {
		super(controllerFactory, processService, LOGGER);
		this.listService = listService;

		/* Inicializa os campos de CPF                     */
		mTxtCpf = new MaskedTextField("###.###.###-##");
		mTxtCpf.setMaxWidth(520.0);

	}

	@FXML
	private void limparFormulario() {
		checkNumber.setSelected(false);
		checkInterested.setSelected(false);
		checkInventaried.setSelected(false);
		checkLawyer.setSelected(false);
		checkCourt.setSelected(false);
		checkJudge.setSelected(false);
		checkSituation.setSelected(false);
		radioNome.setSelected(true);
		cbCourt.getSelectionModel().select(0);
		cbJudge.getSelectionModel().select(0);
		cbSituation.getSelectionModel().select(0);
		txtName.clear();
		mTxtNumber.clear();
		mTxtCpf.clear();
		txtInventaried.clear();
		txtLawyer.clear();
	}

	@Override
	protected void configureForm() {
		preencherChoiceBoxes();
		configRadioButtons();
		configChoiceBoxes();
		configTextFields();

	}

	private void preencherChoiceBoxes() {
		ObservableList<String> obsListaOrgaos = cbCourt.getItems();
		obsListaOrgaos.addAll(listService.getOrganizationsList());
		cbCourt.getSelectionModel().select(0);

		ObservableList<String> obsListaAssuntos = cbJudge.getItems();
		obsListaAssuntos.addAll(listService.getSubjectsDescritionList());
		cbJudge.getSelectionModel().select(0);

		ObservableList<String> obsListaSituacoes = cbSituation.getItems();
		obsListaSituacoes.addAll(listService.getSituationsDescritionList());
		cbSituation.getSelectionModel().select(0);
	}

	private void configRadioButtons() {
		this.tgNomeCpf.selectedToggleProperty().addListener(
				(observavel, valorAnterior, novoValor) -> {
					if(Objects.equals(novoValor, radioNome)) {
						vbInteressado.getChildren().remove(mTxtCpf);
						vbInteressado.getChildren().add(txtName);
					} else {
						vbInteressado.getChildren().remove(txtName);
						vbInteressado.getChildren().add(mTxtCpf);
					}
				});
	}

	private void configChoiceBoxes() {
		cbCourt.getSelectionModel().selectedIndexProperty().addListener(
				(observableValue, oldValue, newValue) -> { 
					if (newValue.intValue() != 0) {
						checkCourt.setSelected(true);
					}
				});
		cbJudge.getSelectionModel().selectedIndexProperty().addListener(
				(observableValue, oldValue, newValue) -> {
					if (newValue.intValue() != 0)
						checkJudge.setSelected(true);
				});
		cbSituation.getSelectionModel().selectedIndexProperty().addListener(
				(observableValue, oldValue, newValue) -> {
					if (newValue.intValue() != 0)
						checkSituation.setSelected(true);
				});
	}

	private void configTextFields() {
		mTxtNumber.focusedProperty().addListener(
				(observableValue, oldValue, newValue) -> {
					if (!newValue && !mTxtNumber.getPlainText().isEmpty()) {
						checkNumber.setSelected(true);
					}
				});
		txtName.focusedProperty().addListener(
				(observableValue, oldValue, newValue) -> {
					if (!newValue && !txtName.getText().isEmpty())
						checkInterested.setSelected(true);
				});
		mTxtCpf.focusedProperty().addListener(
				(observableValue, oldValue, newValue) -> {
					if (!newValue && !mTxtCpf.getPlainText().isEmpty())
						checkInterested.setSelected(true);
				});
		txtInventaried.focusedProperty().addListener((observableValue, oldValue, newValue) -> {
					if (!newValue && !txtInventaried.getText().isEmpty())
						checkInventaried.setSelected(true);
				});
		txtLawyer.focusedProperty().addListener((observableValue, oldValue, newValue) -> {
					if (!newValue && !txtLawyer.getText().isEmpty())
						checkLawyer.setSelected(true);
				});
	}

	@Override
	protected Search mountSearch() {
		String number = (checkNumber.isSelected())? mTxtNumber.getPlainText() : "";
        String name = (checkInterested.isSelected() && radioNome.isSelected())? txtName.getText() : "";
        String cpf = (checkInterested.isSelected() && radioCpf.isSelected())? mTxtCpf.getPlainText() : "";
        String inventaried = checkInventaried.isSelected()? txtInventaried.getText() : "";
        String lawyer = checkLawyer.isSelected()? txtLawyer.getText() : "";
        int idCourt = checkCourt.isSelected()? cbCourt.getSelectionModel().getSelectedIndex() : 0;
        int idJudge = checkJudge.isSelected()? cbJudge.getSelectionModel().getSelectedIndex() : 0;
        int idSituation = checkSituation.isSelected()? cbSituation.getSelectionModel().getSelectedIndex() : 0;
        
        JuridicalProcessSearch search = new JuridicalProcessSearch();
        search.setNumber(number);
        search.setInventorian(name);
        search.setCpf(cpf);
        search.setInventaried(inventaried);
        search.setLawyer(lawyer);
        search.setCourtId(idCourt);
        search.setJudgeId(idJudge);
        search.setSituationId(idSituation);
        
        return search;
	}

	@Override
	protected void configureColumns() {
		tabColNumber.setCellValueFactory(
				content -> new ReadOnlyStringWrapper(content.getValue().getFormattedNumber()));
		tabColInterested.setCellValueFactory(
				content -> new ReadOnlyStringWrapper(((JuridicalInterested)content.getValue().getInventorian()).getName()));
		tabColCourt.setCellValueFactory(
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
