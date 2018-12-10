package presentation;

import business.model.Process;
import business.service.Observer;
import business.service.ProcessService;
import persistence.exception.DatabaseException;
import presentation.utils.StringConstants;
import presentation.utils.widget.ExceptionAlert;
import java.io.IOException;
import java.net.URL;
import java.util.List;
import java.util.ResourceBundle;
import org.apache.log4j.Logger;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.fxml.Initializable;
import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.TableView;
import javafx.stage.Stage;

public abstract class MainScreenCtrl implements Initializable, Observer {

  private final /*@ spec_public nullable @*/ Logger logger;
  private /*@ spec_public nullable @*/ ProcessService processService;
  private /*@ spec_public nullable @*/ ControllerFactory controllerFactory;

  protected /*@ spec_public nullable @*/ Process selectedProcess;

  @FXML
  protected /*@ spec_public nullable @*/ Node root;

  @FXML
  protected /*@ spec_public nullable @*/ Button btnNew;

  @FXML
  protected /*@ spec_public nullable @*/ Button btnEdit;

  @FXML
  protected /*@ spec_public nullable @*/ Button btnPdfDoc;

  @FXML
  protected /*@ spec_public nullable @*/ Button btnDelete;

  @FXML
  protected /*@ spec_public nullable @*/ TableView<Process> tabProcesses;

  public static void showMainScreen(Stage primaryStage, MainScreenCtrl controller) {

    FXMLLoader loader = new FXMLLoader(controller.getFxmlPath());
    loader.setController(controller);
    try {
      Parent rootParent = loader.load();
      primaryStage
          .setScene(new Scene(rootParent, rootParent.prefWidth(-1), rootParent.prefHeight(-1)));
      primaryStage.setTitle(StringConstants.TITLE_APPLICATION.getText());
      primaryStage.show();
    } catch (IOException e) {
      Logger.getLogger(MainScreenCtrl.class).error(e.getMessage(), e);
      ExceptionAlert.show("Não foi possível gerar a tela!",
          primaryStage.sceneProperty().get().getWindow());
    }
  }

  protected MainScreenCtrl(ProcessService processService, ControllerFactory controllerFactory,
      Logger logger) {
    this.processService = processService;
    this.controllerFactory = controllerFactory;
    this.logger = logger;
    this.selectedProcess = null;
  }

  @Override
  public void initialize(URL location, /*@ nullable @*/ResourceBundle resources) {
    processService.attach(this);
    configureTable();
    updateTable();
  }

  @Override
  public void update() {
    updateTable();
  }

  private void configureTable() {
    // eventHandle para detectar o processo selecionado
    tabProcesses.getSelectionModel().selectedItemProperty()
        .addListener((observable, oldValue, newValue) -> {
          selectedProcess = newValue;
          btnEdit.setDisable(newValue != null ? false : true);
          btnPdfDoc.setDisable(newValue != null ? false : true);
          btnDelete.setDisable(newValue != null ? false : true);
        });
    // chama o método abstrato para configurar as colunas
    configureColumns();
  }

  @FXML
  private void showNewProcessEditScreen() {
    ProcessEditCtrl.showProcessEditScreen(root.getScene().getWindow(),
        controllerFactory.createProcessEditCtrl(), null);
  }

  @FXML
  private void showExistentProcessEditScreen() {
    ProcessEditCtrl.showProcessEditScreen(root.getScene().getWindow(),
        controllerFactory.createProcessEditCtrl(), selectedProcess);
  }

  @FXML
  private void showDeleteDialog() {
    DeleteDialogCtrl.showDeleteDialog(root.getScene().getWindow(),
        controllerFactory.createDeleteDialogCtrl(), selectedProcess);
  }

  @FXML
  private void showPdfViewer() {
    PdfViewerCtrl.showPdfViewer(root.getScene().getWindow(),
        controllerFactory.createPdfViewerCtrl(), selectedProcess);
  }

  @FXML
  private void showSearchScreen() {
    SearchScreenCtrl.showSearchScreen(root.getScene().getWindow(),
        controllerFactory.createSearchScreenCtrl());
  }

  @FXML
  private void showStatisticsScreen() {
    StatisticsScreenCtrl.showStatisticsScreen(root.getScene().getWindow(),
        controllerFactory.createStatisticsScreenCtrl());
  }

  private void updateTable() {
    try {
      List<Process> lista = this.processService.pullList();
      tabProcesses.getItems().setAll(lista);
    } catch (DatabaseException e) {
      logger.error(e.getMessage(), e);
      ExceptionAlert.show("ERRO! Contate o administrador do sistema.", root.getScene().getWindow());
    }
  }

  protected abstract void configureColumns();

  public abstract URL getFxmlPath();
}
