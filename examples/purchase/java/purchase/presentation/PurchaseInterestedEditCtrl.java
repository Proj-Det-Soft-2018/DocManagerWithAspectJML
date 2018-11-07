package purchase.presentation;

import java.net.URL;

import org.apache.log4j.Logger;

import business.model.Interested;
import business.service.InterestedService;
import health.presentation.HealthInterestedEditCtrl;
import health.presentation.widget.MaskedContactTextField;
import health.presentation.widget.MaskedTextField;
import javafx.fxml.FXML;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Label;
import javafx.scene.control.TextField;
import presentation.InterestedEditCtrl;
import purchase.model.PurchaseInterested;

public class PurchaseInterestedEditCtrl extends InterestedEditCtrl {
	
	private static final Logger LOGGER = Logger.getLogger(PurchaseInterestedEditCtrl.class);
	private static final URL FXML_PATH = HealthInterestedEditCtrl.class.getResource("/visions/purchase_interested_edit_screen.fxml");

	@FXML
	private Label lblAlert;
	
	@FXML
	private Label lblCnpj;
	
	@FXML
	private TextField txtBusinessName;
	
	@FXML
	private TextField txtLiableName;
	
	@FXML
	private MaskedTextField txtLiableCpf;
	
	@FXML
	private MaskedContactTextField txtContact;
	
	public PurchaseInterestedEditCtrl(InterestedService interestedService) {
		super(interestedService, LOGGER);
	}
	
	@Override
	protected void populeForm() {
		lblCnpj.setText(((PurchaseInterested)super.interested).getFormatedCnpj());
		
		if (super.interested.getId() != null) {
			PurchaseInterested purchaseInterested = (PurchaseInterested)super.interested;
			super.root.getChildren().remove(lblAlert);
			
			txtBusinessName.setText(purchaseInterested.getBusinessName());
			txtLiableName.setText(purchaseInterested.getLiableName());
			txtLiableCpf.setPlainText(purchaseInterested.getLiableCpf());
			txtContact.setContactPlainText(purchaseInterested.getContact());
		}
	}

	@Override
	protected Interested mountInterested() {
		PurchaseInterested interested = new PurchaseInterested();
		interested.setCnpj(((PurchaseInterested)super.interested).getCnpj());
		interested.setBusinessName(txtBusinessName.getText());
		interested.setLiableName(txtLiableName.getText());
		interested.setLiableCpf(txtLiableCpf.plainTextProperty().getValue());
		interested.setContact(txtContact.plainTextProperty().getValue());
		return interested;
	}

	@Override
	protected Scene getDimensionedScene(Parent rootParent) {
		if (interested.getId() == null) {
			return new Scene(rootParent, 400, 330);
		} else {
			return new Scene(rootParent, 400, 300);
		}
	}

	@Override
	public URL getFxmlPath() {
		return FXML_PATH;
	}
}
