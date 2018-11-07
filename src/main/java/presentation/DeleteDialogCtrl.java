package presentation;

import java.io.IOException;
import java.net.URL;
import org.apache.log4j.Logger;
import org.apache.shiro.authc.AuthenticationException;
import persistence.exception.DatabaseException;
import presentation.utils.StringConstants;
import presentation.utils.widget.ExceptionAlert;
import business.model.Process;
import business.service.ProcessService;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Label;
import javafx.scene.control.PasswordField;
import javafx.scene.control.TextField;
import javafx.scene.layout.VBox;
import javafx.scene.paint.Color;
import javafx.stage.Modality;
import javafx.stage.Stage;
import javafx.stage.Window;

/**
 * Classe controladora do dialog de connfirmação de deleção, com o uso de usuário (administrador) e
 * senha.
 * 
 * @author hugo
 */
public class DeleteDialogCtrl {

  private static final URL FXML_PATH =
      DeleteDialogCtrl.class.getResource("/visions/delete_dialog.fxml");
  private static final Logger LOGGER = Logger.getLogger(DeleteDialogCtrl.class);

  /**
   * Processo selecionado para deleção.
   */
  private Process process;
  private ProcessService processService;

  @FXML
  private VBox root;

  /**
   * Campo de texto usado para obtenção do usuário.
   */
  @FXML
  private TextField txtUser;

  /**
   * Campo de texto usado para obtenção da senha.
   */
  @FXML
  private PasswordField txtPassword;

  /**
   * Método estático para exibição o dialog de confirmação de deleção.
   * 
   * @param ownerWindow Tela que chamou este método.
   * @param controller Controlador do dialog.
   * @param process Processo selecionado para deleção.
   */
  public static void showDeleteDialog(Window ownerWindow, DeleteDialogCtrl controller,
      Process process) {
    try {
      FXMLLoader loader = new FXMLLoader(FXML_PATH);
      controller.setProcess(process);
      loader.setController(controller);
      Parent rootParent = loader.load();

      Stage deleteDialogStage = new Stage();
      deleteDialogStage.setTitle(StringConstants.TITLE_DELETE_DIALOG.getText());
      deleteDialogStage.initModality(Modality.WINDOW_MODAL);
      deleteDialogStage.initOwner(ownerWindow);
      deleteDialogStage
          .setScene(new Scene(rootParent, rootParent.prefWidth(-1), rootParent.prefHeight(-1)));

      deleteDialogStage.show();
    } catch (IOException e) {
      LOGGER.error(e.getMessage(), e);
    }
  }

  /**
   * Construtor para objetos {@code DeleteDialogCtrl}.
   * 
   * @param processService Serviço de processos.
   */
  public DeleteDialogCtrl(ProcessService processService) {
    this.processService = processService;
  }

  private void setProcess(Process process) {
    this.process = process;
  }

  /**
   * Método para execução do evento do botão de confirmação de deleção. Nele, obtên-se o usuário e
   * senha inseridos e faz-se a tentativa de deleção, fechando a tela em caso de confirmação ou exi-
   * bindo um alert genérico em caso de usuário ou senha errado ou um {@code ExceptionAlert} em caso
   * de falha no banco.
   */
  @FXML
  private void deleteProcess() {
    String user = txtUser.getText();
    String password = txtPassword.getText();

    try {
      processService.delete(process, user, password);
      this.closeWindow();
    } catch (AuthenticationException ae) {
      Stage selfStage = (Stage) root.getScene().getWindow();
      selfStage.setHeight(250);
      Label errorLabel = new Label(StringConstants.ERROR_PASSWORD.getText());
      errorLabel.setTextFill(Color.RED);
      this.root.getChildren().add(0, errorLabel);
    } catch (DatabaseException e) {
      ExceptionAlert.show("ERRO! Contate o administrador do sistema.", root.getScene().getWindow());
      LOGGER.error(e.getMessage(), e);
    }
  }

  /**
   * Método para execução do evento do botão de cancelamento, ou após a deleção do processo. Este
   * método fecha o dialog.
   */
  @FXML
  private void closeWindow() {
    Stage window = (Stage) root.getScene().getWindow();
    if (window != null)
      window.close();
  }
}
