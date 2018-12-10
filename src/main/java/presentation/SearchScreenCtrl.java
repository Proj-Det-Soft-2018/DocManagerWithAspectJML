package presentation;

import java.io.IOException;
import java.net.URL;
import java.util.List;
import java.util.ResourceBundle;
import org.apache.log4j.Logger;
import business.exception.ValidationException;
import business.model.Process;
import business.model.Search;
import business.service.Observer;
import business.service.ProcessService;
import javafx.application.Platform;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.fxml.Initializable;
import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.TableView;
import javafx.stage.Modality;
import javafx.stage.Stage;
import javafx.stage.Window;
import persistence.exception.DatabaseException;
import presentation.utils.StringConstants;
import presentation.utils.widget.ExceptionAlert;

public abstract class SearchScreenCtrl implements Initializable, Observer {

  private /*@ spec_public nullable @*/ Logger logger;

  private /*@ spec_public nullable @*/ ControllerFactory controllerFactory;
  private /*@ spec_public nullable @*/ ProcessService processService;

  private /*@ spec_public nullable @*/ Process selectedProcess;
  private /*@ spec_public nullable @*/ Search ultimaBusca;

  @FXML
  private /*@ spec_public nullable @*/ Node root;

  @FXML
  protected /*@ spec_public nullable @*/ TableView<Process> tableResultados;

  @FXML
  private /*@ spec_public nullable @*/ Button btnVerEditar;

  @FXML
  private /*@ spec_public nullable @*/ Button btnCertidaoPdf;

  @FXML
  private /*@ spec_public nullable @*/ Button btnApagar;

  public static void showSearchScreen(Window ownerWindow, SearchScreenCtrl controller) {
    try {
      FXMLLoader loader = new FXMLLoader(controller.getFxmlPath());
      loader.setController(controller);
      Parent rootParent = loader.load();

      Stage searchScreen = new Stage();
      searchScreen.initModality(Modality.WINDOW_MODAL);
      searchScreen.initOwner(ownerWindow);
      searchScreen.setTitle(StringConstants.TITLE_SEARCH_SCREEN.getText());
      searchScreen
      .setScene(new Scene(rootParent, rootParent.prefWidth(-1), rootParent.prefHeight(-1)));

      searchScreen.show();
    } catch (IOException e) {
      ExceptionAlert.show("Não foi possível gerar a tela!", ownerWindow);
      Logger.getLogger(SearchScreenCtrl.class).error(e.getMessage(), e);
    }
  }
  
  public SearchScreenCtrl(ControllerFactory controllerFactory, ProcessService processService,
      Logger logger) {
    this.controllerFactory = controllerFactory;
    this.processService = processService;
    this.logger = logger;
    selectedProcess = null;
    ultimaBusca = null;
  }

  @Override
  public void initialize(URL location, /*@ nullable @*/ResourceBundle resources) {
    processService.attach(this);
    configureForm();
    configureTable();
    Platform.runLater(this::configureClosure);
  }

  @Override
  public void update() {
    if (this.ultimaBusca != null) {
      List<Process> resultado = null;
      try {
        resultado = this.processService.searchAll(ultimaBusca);
      } catch (DatabaseException e) {
        ExceptionAlert.show("ERRO! Contate o administrador do sistema.",
            root.getScene().getWindow());
        logger.error(e.getMessage(), e);
      } catch (ValidationException e) {
        ExceptionAlert.show(e.getMessage(), root.getScene().getWindow());
      }
      updateTable(resultado);
    }
  }

  private void configureTable() {
    // eventHandle para detectar o processo selecionado
    tableResultados.getSelectionModel().selectedItemProperty()
    .addListener((observavel, selecionandoAnterior, selecionadoNovo) -> {
      this.selectedProcess = selecionadoNovo;
      this.btnVerEditar.setDisable(selecionadoNovo != null ? false : true);
      this.btnCertidaoPdf.setDisable(selecionadoNovo != null ? false : true);
      this.btnApagar.setDisable(selecionadoNovo != null ? false : true);
    });
    // chama o método abstrato para configurar as colunas
    configureColumns();
  }

  @FXML
  private void search() {

    Search search = mountSearch();
    try {
      List<Process> resultado = processService.searchAll(search);
      ultimaBusca = search;
      updateTable(resultado);
    } catch (ValidationException ve) {
      ExceptionAlert.show(ve.getMessage(), root.getScene().getWindow());
    } catch (DatabaseException e) {
      ExceptionAlert.show("ERRO! Contate o administrador do sistema.", root.getScene().getWindow());
      logger.error(e.getMessage(), e);
    }
  }

  @FXML
  private void closeWindow() {
    Stage window = (Stage) this.root.getScene().getWindow();
    if (window != null)
      window.close();
  }

  private void configureClosure() {
    root.getScene().getWindow().setOnHidden(event -> processService.dettach(this));
  }
  
  private void updateTable(List<Process> processList) {
    tableResultados.getItems().setAll(processList);
  }

  @FXML
  private void showProcessEditScreen() {
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

  protected abstract void configureForm();

  protected abstract Search mountSearch();

  protected abstract void configureColumns();

  public abstract URL getFxmlPath();
}
