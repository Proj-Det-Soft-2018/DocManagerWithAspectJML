package presentation;

import java.io.IOException;
import java.net.URL;
import java.util.ResourceBundle;
import org.apache.log4j.Logger;
import business.exception.ValidationException;
import business.model.Interested;
import business.model.Process;
import business.model.Search;
import business.service.InterestedService;
import business.service.Observer;
import business.service.ProcessService;
import javafx.application.Platform;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.fxml.Initializable;
import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.stage.Modality;
import javafx.stage.Stage;
import javafx.stage.Window;
import persistence.exception.DatabaseException;
import presentation.utils.StringConstants;
import presentation.utils.widget.ExceptionAlert;

 public abstract class ProcessEditCtrl implements Initializable, Observer {

  private /*@ spec_public nullable @*/ Logger logger;

  private /*@ spec_public nullable @*/ ProcessService processService;
  private /*@ spec_public nullable @*/ InterestedService interestedService;
  private /*@ spec_public nullable @*/ ControllerFactory controllerFactory;

  protected /*@ spec_public nullable @*/ Process originalProcess;
  protected /*@ spec_public nullable @*/ Interested interested;

  @FXML
  private /*@ spec_public nullable @*/ Node root;

  public static void showProcessEditScreen(Window ownerWindow, ProcessEditCtrl controller,
      Process process) {
    try {
      FXMLLoader loader = new FXMLLoader(controller.getFxmlPath());
      controller.setOriginalProcess(process);
      loader.setController(controller);
      Parent rootParent = loader.load();

      Stage processEditScreen = new Stage();
      processEditScreen.initModality(Modality.WINDOW_MODAL);
      processEditScreen.initOwner(ownerWindow);
      if (process == null) {
        processEditScreen.setTitle(StringConstants.TITLE_CREATE_PROCESS_SCREEN.getText());
      } else {
        processEditScreen.setTitle(StringConstants.TITLE_EDIT_PROCESS_SCREEN.getText());
      }
      processEditScreen
          .setScene(new Scene(rootParent, rootParent.prefWidth(-1), rootParent.prefHeight(-1)));

      processEditScreen.show();
    } catch (IOException e) {
      ExceptionAlert.show("Não foi possível gerar a tela!", ownerWindow);
      Logger.getLogger(ProcessEditCtrl.class).error(e.getMessage(), e);
    }
  }

  protected ProcessEditCtrl(ProcessService processService, InterestedService interestedService,
      ControllerFactory controllerFactory, Logger logger) {
    this.processService = processService;
    this.interestedService = interestedService;
    this.controllerFactory = controllerFactory;
    this.logger = logger;
    this.originalProcess = null;
    this.interested = null;
  }

  private void setOriginalProcess(/*@ nullable @*/Process originalProcess) {
    this.originalProcess = originalProcess;
  }

  @Override
  public void initialize(URL location, /*@ nullable @*/ResourceBundle resources) {
    interestedService.attach(this);
    initializeForm();
    Platform.runLater(this::configureClosure);
  }

  @Override
  public void update() {
    searchInterestedByUniqueKey();
  }

  @FXML
  private void searchInterestedByUniqueKey() {
    try {
      this.interested = interestedService.search(mountSearch());
      if (interested == null) {
        this.showInterestedCreateScreen();
      } else {
        this.fillInterestedField();
      }
    } catch (ValidationException ve) {
      ExceptionAlert.show(ve.getMessage(), root.getScene().getWindow());
    } catch (DatabaseException e) {
      ExceptionAlert.show("ERRO! Contate o administrador do sistema.", root.getScene().getWindow());
      logger.error(e.getMessage(), e);
    }
  }

  @FXML
  private void showInterestedCreateScreen() {
    Interested newInterested = createInterested();
    InterestedEditCtrl.showIntestedEditScreen(root.getScene().getWindow(),
        controllerFactory.createInterestedEditCtrl(), newInterested);
  }

  @FXML
  protected void showInterestedEditScreen() {
    InterestedEditCtrl.showIntestedEditScreen(root.getScene().getWindow(),
        controllerFactory.createInterestedEditCtrl(), interested);
  }

  @FXML
  protected void clearInterested() {
    interested = null;
    clearInterestedField();
  }

  private void configureClosure() {
    root.getScene().getWindow().setOnHidden(event -> this.interestedService.dettach(this));
  }

  @FXML
  private void closeWindow() {
    Stage janela = (Stage) this.root.getScene().getWindow();
    if (janela != null)
      janela.close();
  }

  @FXML
  private void save() {
    Process editedProcess = mountProcess();
    try {
      if (originalProcess == null) {
        processService.save(editedProcess);
      } else {
        editedProcess.setId(originalProcess.getId());
        processService.update(editedProcess);
      }
      this.closeWindow();
    } catch (ValidationException ve) {
      ExceptionAlert.show(ve.getMessage(), root.getScene().getWindow());
    } catch (DatabaseException e) {
      ExceptionAlert.show("ERRO! Contate o administrador do sistema", root.getScene().getWindow());
      logger.error(e.getMessage(), e);
    }
  }

  
  protected abstract void initializeForm();

  protected abstract Interested createInterested();

  protected abstract Search mountSearch();

  protected abstract void fillInterestedField();

  protected abstract void clearInterestedField();

  protected abstract Process mountProcess();

  public abstract URL getFxmlPath();
}
