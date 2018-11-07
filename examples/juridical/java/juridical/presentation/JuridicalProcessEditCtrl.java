package juridical.presentation;

import java.net.URL;

import org.apache.log4j.Logger;

import business.model.Interested;
import business.model.Process;
import business.model.Search;
import business.service.InterestedService;
import business.service.ListService;
import business.service.ProcessService;
import health.presentation.widget.MaskedTextField;
import javafx.collections.ObservableList;
import javafx.fxml.FXML;
import javafx.scene.control.Button;
import javafx.scene.control.ChoiceBox;
import javafx.scene.control.Label;
import javafx.scene.control.TextArea;
import javafx.scene.control.TextField;
import javafx.scene.layout.HBox;
import juridical.model.JuridicalInterested;
import juridical.model.JuridicalInterestedSearch;
import juridical.model.JuridicalProcess;
import juridical.model.JuridicalSituation;
import presentation.ControllerFactory;
import presentation.ProcessEditCtrl;

public class JuridicalProcessEditCtrl extends ProcessEditCtrl {
	private static final URL FXML_PATH = JuridicalProcessEditCtrl.class.getResource("/visions/juridical_process_edit_screen.fxml");
	private static final Logger LOGGER = Logger.getLogger(JuridicalProcessEditCtrl.class);
	
    private ListService listService;

    @FXML
    private MaskedTextField txtNumber;

    @FXML
    private HBox hBoxInteressado;
    
    @FXML
    private Label lblCpfInteressado;

    @FXML
    private MaskedTextField txtCpfInterested;

    @FXML
    private Button btnBuscarInteressado;

    @FXML
    private Label lblName;

    @FXML
    private Label lblAge;
    
    @FXML
    private Label lblEmail;

    @FXML
    private Label lblContact;
    
    @FXML
    private TextField txtInventoried;
    
    @FXML
    private TextField txtLawyer;
    
    @FXML
    private ChoiceBox<String> cbCourt;

    @FXML
    private ChoiceBox<String> cbJudge;

    @FXML
    private ChoiceBox<String> cbSituation;

    @FXML
    private TextArea txtObservations;

    @FXML
    private Button btnCadastrar;

	protected JuridicalProcessEditCtrl(ListService listService, ProcessService processService,
            InterestedService interestedService, ControllerFactory controllerFactory) {
		super(processService, interestedService, controllerFactory, LOGGER);
		this.listService = listService;
	}

	@Override
	protected void initializeForm() {
		fillChoiceBoxes();
        if (super.originalProcess != null) {
            JuridicalProcess juridicalProcess = (JuridicalProcess)super.originalProcess;
            btnCadastrar.setText("Atualizar");

            txtNumber.setPlainText(juridicalProcess.getNumber());
            txtNumber.setDisable(true);
            
            super.interested = juridicalProcess.getInventorian();
            fillInterestedField();
            
            txtInventoried.setText(juridicalProcess.getInventoriedName());
            txtLawyer.setText(juridicalProcess.getLawyerName());
            cbCourt.getSelectionModel().select(juridicalProcess.getCourt().getId());
            cbJudge.getSelectionModel().select(juridicalProcess.getJudge().getId());
            cbSituation.getSelectionModel().select(juridicalProcess.getSituationString());
            txtObservations.setText(juridicalProcess.getObservation());
        }
	}
	
	private void fillChoiceBoxes() {
        ObservableList<String> obsListaOrgaos = cbCourt.getItems();
        obsListaOrgaos.addAll(listService.getOrganizationsList());
        cbCourt.getSelectionModel().select(0);
    
        ObservableList<String> obsListaAssuntos = cbJudge.getItems();
        obsListaAssuntos.addAll(listService.getSubjectsDescritionList());
        cbJudge.getSelectionModel().select(0);
    
        ObservableList<String> obsListaSituacoes = cbSituation.getItems();
        if(originalProcess != null) {
            obsListaSituacoes.addAll(listService.getSituationsListByCurrentSituation(((JuridicalProcess)super.originalProcess).getSituation()));
        }else {
            obsListaSituacoes.addAll(listService.getSituationsListByCurrentSituation(JuridicalSituation.NULL));
        }
        cbSituation.getSelectionModel().select(0);
    }

	@Override
	protected Interested createInterested() {
		JuridicalInterested interested = new JuridicalInterested();
        interested.setCpf(txtCpfInterested.plainTextProperty().getValue());
        return interested;
	}

	@Override
	protected Search mountSearch() {
		JuridicalInterestedSearch search = new JuridicalInterestedSearch();
        search.setCpf(txtCpfInterested.plainTextProperty().getValue());
        return search;
	}

	@Override
	protected void fillInterestedField() {
		JuridicalInterested juridicalInterested = (JuridicalInterested) super.interested;
        txtCpfInterested.setPlainText(juridicalInterested.getCpf());
        txtCpfInterested.setDisable(true);

        if (hBoxInteressado.getChildren().contains(btnBuscarInteressado)) {
            hBoxInteressado.getChildren().remove(btnBuscarInteressado);

            Button btnEditarInteressado = new Button("Editar");
            btnEditarInteressado.setOnAction(evento -> super.showInterestedEditScreen());
            Button btnLimparInteressado = new Button("Limpar");
            btnLimparInteressado.setOnAction(evento -> super.clearInterested());

            hBoxInteressado.getChildren().addAll(btnEditarInteressado, btnLimparInteressado);
        }

        lblName.setText(juridicalInterested.getName());
        lblAge.setText(""+juridicalInterested.getIdade());
        lblEmail.setText(juridicalInterested.getEmail());
        String contact = juridicalInterested.getFormatedContact();
        if (contact != null && contact.length() != 0) { 
            lblContact.setText(contact);
        } else {
        	lblContact.setText("");
        }

	}

	@Override
	protected void clearInterestedField() {
		hBoxInteressado.getChildren().clear();
        hBoxInteressado.getChildren().addAll(lblCpfInteressado, txtCpfInterested, btnBuscarInteressado);
        txtCpfInterested.setDisable(false);
        txtCpfInterested.clear();
        lblName.setText("");
        lblAge.setText("");
        lblEmail.setText("");
        lblContact.setText("");
	}

	@Override
	protected Process mountProcess() {
		JuridicalProcess process = (JuridicalProcess)super.originalProcess;
		process.setNumber(txtNumber.plainTextProperty().getValue());
		process.setInventorian(super.interested);
		process.setInventoriedName(txtInventoried.getText());
		process.setLawyerName(txtLawyer.getText());
        process.setCourtById(cbCourt.getSelectionModel().getSelectedIndex());
        process.setJudgeById(cbJudge.getSelectionModel().getSelectedIndex());
        process.setSituationById(listService.getSituationsDescritionList()
        		.indexOf(cbSituation.getSelectionModel().getSelectedItem()));
        process.setObservation(txtObservations.getText());
        return process;
	}

	@Override
	public URL getFxmlPath() {
		return FXML_PATH;
	}

}
