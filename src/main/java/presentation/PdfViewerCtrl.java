package presentation;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.net.URL;
import java.util.Base64;
import java.util.ResourceBundle;
import org.apache.commons.io.FilenameUtils;
import org.apache.log4j.Logger;
import business.model.Process;
import business.service.ProcessService;
import javafx.concurrent.Worker;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.fxml.Initializable;
import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.web.WebEngine;
import javafx.scene.web.WebView;
import javafx.stage.FileChooser;
import javafx.stage.Modality;
import javafx.stage.Stage;
import javafx.stage.Window;
import presentation.utils.StringConstants;
import presentation.utils.widget.ExceptionAlert;

/**
 * Classe controladora da tela de visualização e salvamento da certidão em formato Pdf.
 * 
 * @author hugo
 *
 */
public class PdfViewerCtrl implements Initializable {

  private static final Logger LOGGER = Logger.getLogger(PdfViewerCtrl.class);
  private static final URL FXML_PATH =
      PdfViewerCtrl.class.getResource("/visions/pdf_viewer_screen.fxml");

  private ProcessService processService;
  /**
   * Binário do documento Pdf
   */
  private byte[] pdfData;

  @FXML
  private Node root;

  @FXML
  private WebView pdfView;

  /**
   * Método estático para exibição da tela de visualização da certidão em Pdf. Caso ocorra algum
   * erro na montagem da tela este método exibirá um um {@code ExceptionAlert}.
   * 
   * @param ownerWindow Tela que chamou este método.
   * @param controller Controlador do dialog.
   * @param process Processo selecionado para geração da certidão.
   */
  public static void showPdfViewer(Window ownerWindow, PdfViewerCtrl controller, Process process) {
    try {
      FXMLLoader loader = new FXMLLoader(FXML_PATH);
      controller.setProcessPdf(process);
      loader.setController(controller);
      Parent rootParent = loader.load();

      Stage pdfViewerScreen = new Stage();
      pdfViewerScreen.setTitle(StringConstants.TITLE_PDF_VIEWER_SCREEN.getText());
      pdfViewerScreen.initModality(Modality.WINDOW_MODAL);
      pdfViewerScreen.initOwner(ownerWindow);
      pdfViewerScreen
          .setScene(new Scene(rootParent, rootParent.prefWidth(-1), rootParent.prefHeight(-1)));

      pdfViewerScreen.show();
    } catch (IOException e) {
      LOGGER.error(e.getMessage(), e);
    }
  }

  /**
   * Construtor para objetos {@code PdfViewerCtrl}.
   * 
   * @param processService Serviço de processos.
   */
  public PdfViewerCtrl(ProcessService processService) {
    this.processService = processService;
  }

  /**
   * Método para geração do binário do documento do processo fornecido por parâmetro.
   * 
   * @param targetProcess Processo que se deseja gerar a certidão
   */
  private void setProcessPdf(Process targetProcess) {
    pdfData = processService.getPdf(targetProcess);
  }

  /*
   * (non-Javadoc)
   * 
   * @see javafx.fxml.Initializable#initialize(java.net.URL, java.util.ResourceBundle)
   */
  @Override
  public void initialize(URL location, ResourceBundle resources) {
    configureEngine();
  }

  /**
   * Método para configuração do {@code javafx.scene.web.WebEngine} do webView utilizado para vi-
   * sualizar o arquivo pdf. Basicamente configura para carregar o arquivo assim que o webView este-
   * ja pronto.
   */
  private void configureEngine() {

    WebEngine engine = pdfView.getEngine();

    // Setando a página para o visualizador de PDF
    String url = getClass().getResource("/pdfjs/web/viewer.html").toExternalForm();
    engine.setJavaScriptEnabled(true);
    engine.load(url);

    engine.getLoadWorker().stateProperty().addListener((obs, oldState, newState) -> {
      if (newState == Worker.State.SUCCEEDED) {
        loadPdfFile();
      }
    });
  }

  /**
   * Método para execução do evento do botão de voltar ou quando salvar o arquivo. Este método fecha
   * a tela.
   */
  @FXML
  private void closeWindow() {
    Stage window = (Stage) root.getScene().getWindow();
    if (window != null)
      window.close();
  }

  /**
   * Método para execução do evento do botão "Salvar". Este método cria uma nova janela com o
   * {@code javafx.stage.FileChooser} para geração de um arquivo ({@code java.io.File} de destino.
   */
  @FXML
  private void savePdfFile() {
    FileChooser fileChooser = new FileChooser();

    // Set extension filter for text files
    FileChooser.ExtensionFilter extFilter =
        new FileChooser.ExtensionFilter("arquivos PDF (*.pdf)", "*.pdf");
    fileChooser.getExtensionFilters().add(extFilter);
    fileChooser.setTitle(StringConstants.TITTLE_PDF_SAVE_SCREEN.getText());
    fileChooser.setInitialFileName("Certidão.pdf");

    // Show save file dialog
    File outputFile = fileChooser.showSaveDialog(root.getScene().getWindow());

    if (outputFile != null) {
      // Testa a extenção do arquivo de destino e troca, quando necessário
      if (!FilenameUtils.getExtension(outputFile.getName()).equalsIgnoreCase("pdf")) {
        outputFile = new File(outputFile.getParentFile(),
            FilenameUtils.getBaseName(outputFile.getName()) + ".pdf");
      }
      savePdfToFile(outputFile);
      closeWindow();
    }
  }

  /**
   * Carrega o binário do documento Pdf no visualizador do {@code javafx.scene.web.WebView}.
   */
  private void loadPdfFile() {
    String pdfBase64 = Base64.getEncoder().encodeToString(pdfData);
    pdfView.getEngine().executeScript("openFileFromBase64('" + pdfBase64 + "')");
  }

  /**
   * Salva as informações do binário do documento Pdf no arquivo ({@code java.io.File}) fornecido.
   * 
   * @param outputFile Arquivo de destino.
   */
  private void savePdfToFile(File outputFile) {
    try (FileOutputStream fos = new FileOutputStream(outputFile)) {
      fos.write(pdfData);
    } catch (IOException e) {
      ExceptionAlert.show("Falha ao tentar salvar o arquivo!", root.getScene().getWindow());
      LOGGER.error(e.getMessage(), e);
    }
  }
}
