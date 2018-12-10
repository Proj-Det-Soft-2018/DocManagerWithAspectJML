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

public class PdfViewerCtrl implements Initializable {

  private static final /*@ spec_public nullable @*/  Logger LOGGER = Logger.getLogger(PdfViewerCtrl.class);
  private static final /*@ spec_public nullable @*/  URL FXML_PATH = PdfViewerCtrl.class.getResource("/visions/pdf_viewer_screen.fxml");

  private /*@ spec_public nullable @*/  ProcessService processService;
  private /*@ spec_public nullable @*/  byte[] pdfData;

  @FXML
  private /*@ spec_public nullable @*/  Node root;

  @FXML
  private /*@ spec_public nullable @*/  WebView pdfView;

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

  public PdfViewerCtrl(ProcessService processService) {
    this.processService = processService;
  }

  private void setProcessPdf(Process targetProcess) {
    pdfData = processService.getPdf(targetProcess);
  }

  @Override
  public void initialize(URL location, /*@ nullable @*/ResourceBundle resources) {
    configureEngine();
  }

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

  @FXML
  private void closeWindow() {
    Stage window = (Stage) root.getScene().getWindow();
    if (window != null)
      window.close();
  }

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

  private void loadPdfFile() {
    String pdfBase64 = Base64.getEncoder().encodeToString(pdfData);
    pdfView.getEngine().executeScript("openFileFromBase64('" + pdfBase64 + "')");
  }

  private void savePdfToFile(File outputFile) {
    try (FileOutputStream fos = new FileOutputStream(outputFile)) {
      fos.write(pdfData);
    } catch (IOException e) {
      ExceptionAlert.show("Falha ao tentar salvar o arquivo!", root.getScene().getWindow());
      LOGGER.error(e.getMessage(), e);
    }
  }
}
