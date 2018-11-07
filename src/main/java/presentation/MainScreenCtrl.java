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

/**
 * Classe abstrata para controlador da tela principal. Como é um dos pontos flexíveis do framework,
 * o desenvolvedor deve implementar seus métodos abstratos para obter um controlador para a tela que
 * exibe os botões de navegação e tabela de escolha dos processos.
 * 
 * @author hugotho
 */
public abstract class MainScreenCtrl implements Initializable, Observer {

  private final Logger logger;
  private ProcessService processService;
  /**
   * Fábrica utilizada para criação dos controladores das telas que são acessadas pela tela
   * principal.
   */
  private ControllerFactory controllerFactory;

  protected Process selectedProcess;

  @FXML
  protected Node root;

  @FXML
  protected Button btnNew;

  @FXML
  protected Button btnEdit;

  @FXML
  protected Button btnPdfDoc;

  @FXML
  protected Button btnDelete;

  @FXML
  protected TableView<Process> tabProcesses;

  /**
   * Método estático para exibição da tela principal. Caso ocorra algum erro na montagem da tela
   * este método exibirá um um {@code ExceptionAlert}.
   * 
   * @param primaryStage Placo inicial obtivo através do parâmetro do método start da aplicação
   *        JavaFX
   * @param controller Controlador da tela.
   */
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

  /**
   * Construtor que deve ser chamado pelas classes que extendam {@code InterestedEditCtrl}.
   * 
   * @param processService Serviço de processos
   * @param controllerFactory Fábrica de controladores
   * @param logger {@code org.apache.log4j.Logger} para efetuação de logs.
   */
  protected MainScreenCtrl(ProcessService processService, ControllerFactory controllerFactory,
      Logger logger) {
    this.processService = processService;
    this.controllerFactory = controllerFactory;
    this.logger = logger;
    this.selectedProcess = null;
  }

  /*
   * (non-Javadoc)
   * 
   * @see javafx.fxml.Initializable#initialize(java.net.URL, java.util.ResourceBundle)
   */
  @Override
  public void initialize(URL location, ResourceBundle resources) {
    processService.attach(this);
    configureTable();
    updateTable();
  }

  /*
   * (non-Javadoc)
   * 
   * @see business.service.Observer#update()
   */
  @Override
  public void update() {
    updateTable();
  }

  /**
   * Método para configuração de captura de eventos da tabela de processos.
   */
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

  /**
   * Método para execução do evento de clique no botão "Novo", consiste em mostrar a tela de edição
   * de processos para um novo processo.
   */
  @FXML
  private void showNewProcessEditScreen() {
    ProcessEditCtrl.showProcessEditScreen(root.getScene().getWindow(),
        controllerFactory.createProcessEditCtrl(), null);
  }

  /**
   * Método para execução do evento de clique no botão "Ver/Editar", consiste em mostrar a tela de
   * edição de processos para um processo existente selecionado na tabela.
   */
  @FXML
  private void showExistentProcessEditScreen() {
    ProcessEditCtrl.showProcessEditScreen(root.getScene().getWindow(),
        controllerFactory.createProcessEditCtrl(), selectedProcess);
  }

  /**
   * Método para execução do evento de clique no botão "Apagar", consiste em mostrar um dialog para
   * confimação com senha para exclusão do processo selecionado.
   */
  @FXML
  private void showDeleteDialog() {
    DeleteDialogCtrl.showDeleteDialog(root.getScene().getWindow(),
        controllerFactory.createDeleteDialogCtrl(), selectedProcess);
  }

  /**
   * Método para execução do evento de clique no botão "Certidão Pdf", consiste em mostrar a tela de
   * visualização de Pdf com o arquivo preparado com o processo selecionado.
   */
  @FXML
  private void showPdfViewer() {
    PdfViewerCtrl.showPdfViewer(root.getScene().getWindow(),
        controllerFactory.createPdfViewerCtrl(), selectedProcess);
  }

  /**
   * Método para execução do evento de clique no botão "Buscar", consiste em mostrar a tela de
   * busca.
   */
  @FXML
  private void showSearchScreen() {
    SearchScreenCtrl.showSearchScreen(root.getScene().getWindow(),
        controllerFactory.createSearchScreenCtrl());
  }

  /**
   * Método para execução do evento de clique no botão "Estatísticas", consiste em mostrar a tela de
   * estatísticas do sistema.
   */
  @FXML
  private void showStatisticsScreen() {
    StatisticsScreenCtrl.showStatisticsScreen(root.getScene().getWindow(),
        controllerFactory.createStatisticsScreenCtrl());
  }

  /**
   * Obtém, pelo serviço de processos, a lista de processos atualizada e atualiza a exibição na ta-
   * bela. Exibe um {@code ExceptionAlert} em caso de erro.
   */
  private void updateTable() {
    try {
      List<Process> lista = this.processService.pullList();
      tabProcesses.getItems().setAll(lista);
    } catch (DatabaseException e) {
      logger.error(e.getMessage(), e);
      ExceptionAlert.show("ERRO! Contate o administrador do sistema.", root.getScene().getWindow());
    }
  }

  /**
   * Método abstrato que deve ser implementado para configurar a forma de preenchimento das linhas
   * da tabela com os objetos específicos de cada aplicação.
   */
  protected abstract void configureColumns();

  /**
   * Método abstrato para obtenção do caminho para o arquivo .fxml da tela principal.
   */
  public abstract URL getFxmlPath();
}
