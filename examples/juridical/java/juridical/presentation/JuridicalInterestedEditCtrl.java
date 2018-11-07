package juridical.presentation;

import java.net.URL;

import org.apache.log4j.Logger;

import business.model.Interested;
import business.service.InterestedService;
import health.presentation.widget.MaskedContactTextField;
import javafx.fxml.FXML;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Label;
import javafx.scene.control.TextField;
import juridical.model.JuridicalInterested;
import presentation.InterestedEditCtrl;

public class JuridicalInterestedEditCtrl extends InterestedEditCtrl {
	private static final Logger LOGGER = Logger.getLogger(JuridicalInterestedEditCtrl.class);
	private static final URL FXML_PATH = JuridicalInterestedEditCtrl.class.getResource("/visions/juridical_interested_edit_screen.fxml");

	@FXML
	private Label lblAlert;

	@FXML
	private Label lblCpf;

	@FXML
	private TextField txtName;

	@FXML
	private TextField txtAge;

	@FXML
	private TextField txtEmail;

	@FXML
	private MaskedContactTextField txtContact;

	protected JuridicalInterestedEditCtrl(InterestedService interestedService) {
		super(interestedService, LOGGER);
	}

	@Override
	protected void populeForm() {
		lblCpf.setText(((JuridicalInterested)super.interested).getFormatedCpf());

		if (super.interested.getId() != null) {
			JuridicalInterested juridicalInterested = (JuridicalInterested)super.interested;
			super.root.getChildren().remove(lblAlert);

			txtName.setText(juridicalInterested.getName());
			txtAge.setText(""+juridicalInterested.getIdade());
			txtEmail.setText(juridicalInterested.getEmail());
			txtContact.setContactPlainText(juridicalInterested.getContact());
		}

	}

	@Override
	protected Interested mountInterested() {
		JuridicalInterested interested = new JuridicalInterested();
		interested.setCpf(((JuridicalInterested)super.interested).getCpf());
		interested.setName(txtName.getText());
		interested.setIdade(Integer.parseInt(txtAge.getText()));
		interested.setEmail(txtEmail.getText());
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
