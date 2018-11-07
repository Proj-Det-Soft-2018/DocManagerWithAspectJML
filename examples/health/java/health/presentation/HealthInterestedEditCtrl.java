package health.presentation;

import java.net.URL;

import org.apache.log4j.Logger;

import business.model.Interested;
import business.service.InterestedService;
import health.model.HealthInterested;
import health.presentation.widget.MaskedContactTextField;
import javafx.fxml.FXML;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Label;
import javafx.scene.control.TextField;
import presentation.InterestedEditCtrl;

public class HealthInterestedEditCtrl extends InterestedEditCtrl {
	
	private static final Logger LOGGER = Logger.getLogger(HealthInterestedEditCtrl.class);
	private static final URL FXML_PATH = HealthInterestedEditCtrl.class.getResource("/visions/health_interested_edit_screen.fxml");
	
	@FXML
	private Label lblAlert;
	
	@FXML
	private Label lblTxtCpf;
	
	@FXML
	private TextField txtName;
	
	@FXML
	private MaskedContactTextField txtContact;
	
	public HealthInterestedEditCtrl(InterestedService interestedService) {
		super(interestedService, LOGGER);
	}
	
	@Override
	protected Scene getDimensionedScene(Parent rootParent) {
		if (interested.getId() == null) {
			return new Scene(rootParent, 400, 260);
		} else {
			return new Scene(rootParent, 400, 230);
		}
	}
	
	@Override
	protected void populeForm() {
		lblTxtCpf.setText(((HealthInterested)interested).getFormatedCpf());
		
		if (interested.getId() != null) {
			HealthInterested healthInterested = (HealthInterested) interested;
			super.root.getChildren().remove(lblAlert);
			
			txtName.setText(healthInterested.getName());
			txtContact.setContactPlainText(healthInterested.getContact());
		}
	}
	
	@Override
	protected Interested mountInterested() {
		return new HealthInterested(
				txtName.getText(),
				((HealthInterested)super.interested).getCpf(),
				txtContact.plainTextProperty().getValue()
				);
	}

	@Override
	public URL getFxmlPath() {
		return FXML_PATH;
	}

}
