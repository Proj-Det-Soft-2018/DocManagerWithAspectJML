package purchase.presentation;

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
import presentation.ControllerFactory;
import presentation.ProcessEditCtrl;
import purchase.model.PurchaseInterested;
import purchase.model.PurchaseInterestedSearch;
import purchase.model.PurchaseProcess;
import purchase.model.PurchaseSituation;

public class PurchaseProcessEditCtrl extends ProcessEditCtrl {

	private static final URL FXML_PATH = PurchaseProcessEditCtrl.class.getResource("/visions/purchase_process_edit_screen.fxml");
    private static final Logger LOGGER = Logger.getLogger(PurchaseProcessEditCtrl.class);
	
    private ListService listService;

    @FXML
    private MaskedTextField txtNumber;
    
    @FXML
    private TextField txtDescription;

    @FXML
    private HBox hBoxInteressado;
    
    @FXML
    private Label lblCnpjInteressado;

    @FXML
    private MaskedTextField txtCnpjInterested;

    @FXML
    private Button btnBuscarInteressado;

    @FXML
    private Label lblBusinessName;

    @FXML
    private Label lblContact;
    
    @FXML
    private Label lblLiableName;

    @FXML
    private Label lblLiableCpf;
    
    @FXML
    private ChoiceBox<String> cbOriginEntity;

    @FXML
    private ChoiceBox<String> cbType;

    @FXML
    private ChoiceBox<String> cbSituation;

    @FXML
    private TextArea txtObservations;

    @FXML
    private Button btnCadastrar;

    public PurchaseProcessEditCtrl(ListService listService, ProcessService processService,
            InterestedService interestedService, ControllerFactory controllerFactory) {
        super(processService, interestedService, controllerFactory, LOGGER);
        this.listService = listService;
    }
    
	@Override
	protected void initializeForm() {
		fillChoiceBoxes();
        if (super.originalProcess != null) {
            PurchaseProcess purchaseProcess = (PurchaseProcess)super.originalProcess;
            btnCadastrar.setText("Atualizar");

            txtNumber.setPlainText(purchaseProcess.getNumber());
            txtNumber.setDisable(true);
            txtDescription.setText(purchaseProcess.getDescription());
            
            super.interested = purchaseProcess.getInterested();
            fillInterestedField();
            
            cbOriginEntity.getSelectionModel().select(purchaseProcess.getOriginEntity().getId());
            cbType.getSelectionModel().select(purchaseProcess.getSubject().getId());
            cbSituation.getSelectionModel().select(purchaseProcess.getSituationString());
            txtObservations.setText(purchaseProcess.getObservation());
        }
	}
	
	private void fillChoiceBoxes() {
        ObservableList<String> obsListaOrgaos = cbOriginEntity.getItems();
        obsListaOrgaos.addAll(listService.getOrganizationsList());
        cbOriginEntity.getSelectionModel().select(0);
    
        ObservableList<String> obsListaAssuntos = cbType.getItems();
        obsListaAssuntos.addAll(listService.getSubjectsDescritionList());
        cbType.getSelectionModel().select(0);
    
        ObservableList<String> obsListaSituacoes = cbSituation.getItems();
        if(originalProcess != null) {
            obsListaSituacoes.addAll(listService.getSituationsListByCurrentSituation(((PurchaseProcess)super.originalProcess).getSituation()));
        }else {
            obsListaSituacoes.addAll(listService.getSituationsListByCurrentSituation(PurchaseSituation.NULL));
        }
        cbSituation.getSelectionModel().select(0);
    }

	@Override
	protected Interested createInterested() {
        PurchaseInterested interested = new PurchaseInterested();
        interested.setCnpj(txtCnpjInterested.plainTextProperty().getValue());
        return interested;
    }

	@Override
	protected Search mountSearch() {
        PurchaseInterestedSearch search = new PurchaseInterestedSearch();
        search.setCnpj(txtCnpjInterested.plainTextProperty().getValue());
        return search; 
    }

	@Override
	protected void fillInterestedField() {
		PurchaseInterested purchaseInterested = (PurchaseInterested) super.interested;
        txtCnpjInterested.setPlainText(purchaseInterested.getCnpj());
        txtCnpjInterested.setDisable(true);

        if (hBoxInteressado.getChildren().contains(btnBuscarInteressado)) {
            hBoxInteressado.getChildren().remove(btnBuscarInteressado);

            Button btnEditarInteressado = new Button("Editar");
            btnEditarInteressado.setOnAction(evento -> super.showInterestedEditScreen());
            Button btnLimparInteressado = new Button("Limpar");
            btnLimparInteressado.setOnAction(evento -> super.clearInterested());

            hBoxInteressado.getChildren().addAll(btnEditarInteressado, btnLimparInteressado);
        }

        lblBusinessName.setText(purchaseInterested.getBusinessName());
        String contact = purchaseInterested.getFormatedContact();
        if (contact != null && contact.length() != 0) { 
            lblContact.setText(contact);
        } else {
        	lblContact.setText("");
        }
        lblLiableName.setText(purchaseInterested.getLiableName());
        lblLiableCpf.setText(purchaseInterested.getFormatedLiableCpf());
	}

	@Override
	protected void clearInterestedField() {
        hBoxInteressado.getChildren().clear();
        hBoxInteressado.getChildren().addAll(lblCnpjInteressado, txtCnpjInterested, btnBuscarInteressado);
        txtCnpjInterested.setDisable(false);
        txtCnpjInterested.clear();
        lblBusinessName.setText("");
        lblContact.setText("");
        lblLiableName.setText("");
        lblLiableCpf.setText("");
    }

	@Override
	protected Process mountProcess() {
		PurchaseProcess process = new PurchaseProcess();
		process.setNumber(txtNumber.plainTextProperty().getValue());
		process.setDescription(txtDescription.getText());
        process.setInterested(super.interested);
        process.setOriginEntityById(cbOriginEntity.getSelectionModel().getSelectedIndex());
        process.setSubjectById(cbType.getSelectionModel().getSelectedIndex());
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
