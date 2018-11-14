package presentation;

import java.net.URL;
import java.util.Objects;

import org.apache.log4j.Logger;

import business.model.HealthInterested;
import business.model.HealthProcess;
import business.model.HealthProcessSearch;
import business.model.Search;
import business.service.ListService;
import business.service.ProcessService;
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
import presentation.utils.DateUtil;
import presentation.utils.widget.DynamicMaskTextField;
import presentation.utils.widget.MaskedTextField;

public class HealthSearchScreenCtrl extends SearchScreenCtrl {

    private static final URL FXML_PATH = HealthSearchScreenCtrl.class.getResource("/visions/health_process_search_screen.fxml");
	private static final Logger LOGGER = Logger.getLogger(HealthSearchScreenCtrl.class);
	
	private ListService listService;
	
	private MaskedTextField mTxtCpf;
	private DynamicMaskTextField dmTxtOficioNum;

	@FXML
	private VBox vbNumero;

	@FXML
	private VBox vbInteressado;

	@FXML
	private CheckBox checkNumero;

	@FXML
	private CheckBox checkInteressado;

	@FXML
	private CheckBox checkOrgao;

	@FXML
	private CheckBox checkAssunto;

	@FXML
	private CheckBox checkSituacao;

	@FXML
	private ToggleGroup tgProcessoOficio;

	@FXML
	private ToggleGroup tgNomeCpf;

	@FXML
	private RadioButton radioProcesso;

	@FXML
	private RadioButton radioOficio;

	@FXML
	private RadioButton radioNome;

	@FXML
	private RadioButton radioCpf;

	@FXML
	private MaskedTextField mTxtProcessoNum;

	@FXML
	private TextField txtNome;

	@FXML
	private ChoiceBox<String> choiceOrgao;

	@FXML
	private ChoiceBox<String> choiceAssunto;

	@FXML
	private ChoiceBox<String> choiceSituacao;

	@FXML
	private TableColumn<HealthProcess, String> tabColTipo;

	@FXML
	private TableColumn<HealthProcess, String> tabColNumero;

	@FXML
	private TableColumn<HealthProcess, String> tabColInteressado;

	@FXML
	private TableColumn<HealthProcess, String> tabColSituacao;

    @FXML
    private TableColumn<HealthProcess, String> tabColumnRegDate;
	
	public HealthSearchScreenCtrl(ProcessService processService, ListService listService,
	        ControllerFactory controllerFactory) {
        super(controllerFactory, processService, LOGGER);
        this.listService = listService;
        
        /* Inicializa os campos de número de Ofício e CPF                     */
        mTxtCpf = new MaskedTextField("###.###.###-##");
        mTxtCpf.setMaxWidth(520.0);
        dmTxtOficioNum = new DynamicMaskTextField("####/####-*", 9);
        dmTxtOficioNum.setMaxWidth(520.0);
    }

	@FXML
	private void limparFormulario() {
		checkNumero.setSelected(false);
		checkInteressado.setSelected(false);
		checkOrgao.setSelected(false);
		checkAssunto.setSelected(false);
		checkSituacao.setSelected(false);
		radioProcesso.setSelected(true);
		radioNome.setSelected(true);
		choiceOrgao.getSelectionModel().select(0);
		choiceAssunto.getSelectionModel().select(0);
		choiceSituacao.getSelectionModel().select(0);
		txtNome.clear();
		mTxtProcessoNum.clear();
		mTxtCpf.clear();
		dmTxtOficioNum.clear();
		dmTxtOficioNum.setDynamic(true);
	}

	@Override
	protected void configureForm() {
		preencherChoiceBoxes();
		configurarRadioButtons();
		configurarChoiceBoxOrgao();
		configurarChoiceBoxAssunto();
		configurarChoiceBoxSituacao();
		configurarCheckBoxOrgao();
		configurarTextFieldsNumeroProcesso();
		configurarTextFieldsInteressado();
	}

	private void preencherChoiceBoxes() {
		ObservableList<String> obsListaOrgaos = choiceOrgao.getItems();
		obsListaOrgaos.addAll(listService.getOrganizationsList());
		choiceOrgao.getSelectionModel().select(0);

		ObservableList<String> obsListaAssuntos = choiceAssunto.getItems();
		obsListaAssuntos.addAll(listService.getSubjectsDescritionList());
		choiceAssunto.getSelectionModel().select(0);

		ObservableList<String> obsListaSituacoes = choiceSituacao.getItems();
		obsListaSituacoes.addAll(listService.getSituationsDescritionList());
		choiceSituacao.getSelectionModel().select(0);
	}

	private void configurarRadioButtons() {
		tgProcessoOficio.selectedToggleProperty().addListener(
				(observavel, valorAnterior, novoValor) ->  {
					if(Objects.equals(novoValor, radioProcesso)) {
						this.vbNumero.getChildren().remove(this.dmTxtOficioNum);
						this.vbNumero.getChildren().add(this.mTxtProcessoNum);
					} else {
						this.vbNumero.getChildren().remove(this.mTxtProcessoNum);
						this.vbNumero.getChildren().add(this.dmTxtOficioNum);
					}

				});
		this.tgNomeCpf.selectedToggleProperty().addListener(
				(observavel, valorAnterior, novoValor) -> {
					if(Objects.equals(novoValor, radioNome)) {
						vbInteressado.getChildren().remove(mTxtCpf);
						vbInteressado.getChildren().add(txtNome);
					} else {
						vbInteressado.getChildren().remove(txtNome);
						vbInteressado.getChildren().add(mTxtCpf);
					}
				});
	}

	private void configurarChoiceBoxOrgao() {
		choiceOrgao.getSelectionModel().selectedIndexProperty().addListener(
				(observableValue, oldValue, newValue) -> { 
					if (newValue.intValue() == 0) {
						dmTxtOficioNum.setDynamic(true);
						if (oldValue.intValue() != 0 && maskIsCompletelyFilled(dmTxtOficioNum, "#")) {	
							int oldIndex = oldValue.intValue();
							StringBuilder newText = new StringBuilder(dmTxtOficioNum.getPlainText());

							newText.append(choiceOrgao.getItems().get(oldIndex).split(" - ")[0]);
							dmTxtOficioNum.adjustMask(newText.length());
							dmTxtOficioNum.setPlainText(newText.toString());
						}
					} else {
						if (!checkOrgao.isSelected()) {
							checkOrgao.setSelected(true);
						}
						int newIndex = newValue.intValue();
						String initials = choiceOrgao.getItems().get(newIndex).split(" - ")[0];
						dmTxtOficioNum.setDynamic(false);
						dmTxtOficioNum.setMask("####/####-" + initials);
					}
				});
	}

	private void configurarChoiceBoxAssunto() {
		choiceAssunto.getSelectionModel().selectedIndexProperty().addListener(
				(observableValue, oldValue, newValue) -> {
					if (newValue.intValue() != 0)
						checkAssunto.setSelected(true);
				});
	}

	private void configurarChoiceBoxSituacao() {
		choiceSituacao.getSelectionModel().selectedIndexProperty().addListener(
				(observableValue, oldValue, newValue) -> {
					if (newValue.intValue() != 0)
						checkSituacao.setSelected(true);
				});
	}

	private void configurarCheckBoxOrgao() {
		checkOrgao.selectedProperty().addListener(
				(valorObservado, valorAntigo, valorNovo) -> {
					if (valorNovo && choiceOrgao.getSelectionModel().getSelectedIndex() != 0) {
						dmTxtOficioNum.setDynamic(false);
						String orgao = choiceOrgao.getSelectionModel().getSelectedItem();
						dmTxtOficioNum.setMask("####/####-" + orgao.split(" - ")[0]);

					} else {
						dmTxtOficioNum.setDynamic(true);
						boolean validChoice = choiceOrgao.getSelectionModel().getSelectedIndex() != 0;

						if (validChoice && maskIsCompletelyFilled(dmTxtOficioNum, "#")) {
							StringBuilder newText = new StringBuilder(dmTxtOficioNum.getPlainText());
							String initials = choiceOrgao.getSelectionModel().getSelectedItem().split(" - ")[0];

							newText.append(initials);
							dmTxtOficioNum.adjustMask(newText.length());
							dmTxtOficioNum.setPlainText(newText.toString());
						}
					}
				});
	}
	
	private boolean maskIsCompletelyFilled (MaskedTextField mTextField, String maskChar) {
        String mask = mTextField.getMask();
        int maskFillingLength = mask.length() - mask.replaceAll(maskChar, "").length();
        int plainTextLength = mTextField.getPlainText().length();

        return (plainTextLength == maskFillingLength);
    }

	private void configurarTextFieldsNumeroProcesso() {
		mTxtProcessoNum.focusedProperty().addListener(
				(observableValue, oldValue, newValue) -> {
					if (!newValue && !mTxtProcessoNum.getPlainText().isEmpty())
						checkNumero.setSelected(true);
				});

		dmTxtOficioNum.focusedProperty().addListener(
				(observableValue, oldValue, newValue) -> {
					if (!newValue && !dmTxtOficioNum.getPlainText().isEmpty())
						checkNumero.setSelected(true);
				});
	}

	private void configurarTextFieldsInteressado() {
		txtNome.focusedProperty().addListener(
				(observableValue, oldValue, newValue) -> {
					if (!newValue && !txtNome.getText().isEmpty())
						checkInteressado.setSelected(true);
				});
		mTxtCpf.focusedProperty().addListener(
				(observableValue, oldValue, newValue) -> {
					if (!newValue && !mTxtCpf.getPlainText().isEmpty())
						checkInteressado.setSelected(true);
				});
	}

	@Override
	protected void configureColumns() {
		// inicia as colunas
		tabColTipo.setCellValueFactory(
				conteudo -> new ReadOnlyStringWrapper(conteudo.getValue().getType()));
		tabColNumero.setCellValueFactory(
				conteudo -> new ReadOnlyStringWrapper(conteudo.getValue().getFormattedNumber()));
		tabColInteressado.setCellValueFactory(
				conteudo -> new ReadOnlyStringWrapper(((HealthInterested)conteudo.getValue().getIntersted()).getName()));
		tabColSituacao.setCellValueFactory(
				conteudo -> new ReadOnlyStringWrapper(conteudo.getValue().getSituation().getDescription()));
        tabColumnRegDate.setCellValueFactory(
                content -> new ReadOnlyStringWrapper(DateUtil.format(content.getValue().getRegistrationDate())));
	}

    @Override
    protected Search mountSearch() {
        String numProcesso = (checkNumero.isSelected())? getProcessNumberEntry() : "";
        String nomeInteressado = (checkInteressado.isSelected() && radioProcesso.isSelected())? txtNome.getText() : "";
        String cpfInteressado = (checkInteressado.isSelected() && radioCpf.isSelected())? mTxtCpf.getPlainText() : "";
        int idOrgao = checkOrgao.isSelected()? choiceOrgao.getSelectionModel().getSelectedIndex() : 0;
        int idAssunto = checkAssunto.isSelected()? choiceAssunto.getSelectionModel().getSelectedIndex() : 0;
        int idSituacao = checkSituacao.isSelected()? choiceSituacao.getSelectionModel().getSelectedIndex() : 0;
        
        HealthProcessSearch search = new HealthProcessSearch();
        search.setNumber(numProcesso);
        search.setName(nomeInteressado);
        search.setCpf(cpfInteressado);
        search.setOrganizationId(idOrgao);
        search.setSubjectId(idAssunto);
        search.setSituationId(idSituacao);
        
        return search;
    }
    
    private String getProcessNumberEntry() {
        if (radioProcesso.isSelected()) {
            return mTxtProcessoNum.plainTextProperty().getValue();
        }

        StringBuilder numProcesso = new StringBuilder();
        numProcesso.append(mTxtProcessoNum.plainTextProperty().getValue());
        if (checkOrgao.isSelected() && choiceOrgao.getSelectionModel().getSelectedIndex() != 0) {
            numProcesso.append(choiceOrgao.getSelectionModel().getSelectedItem().split("-")[0]);
        }
        return numProcesso.toString();
    }
    
    @Override
    public URL getFxmlPath() {
        return FXML_PATH;
    }
}
