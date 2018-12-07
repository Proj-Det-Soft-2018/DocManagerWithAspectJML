package presentation.utils.widget;

import javafx.scene.control.Alert;
import javafx.scene.control.Label;
import javafx.scene.control.Alert.AlertType;
import javafx.scene.layout.Region;
import javafx.scene.paint.Color;
import javafx.stage.Window;

public class ExceptionAlert {
  
  public static void show(String message, Window ownerWindow) {
    Alert alert = new Alert(AlertType.ERROR, message);
    alert.getDialogPane().getChildren().stream().filter(node -> node instanceof Label)
        .forEach(node -> {
          ((Label) node).setMinHeight(Region.USE_PREF_SIZE);
          ((Label) node).setTextFill(Color.RED);
        });
    alert.setHeaderText(null);
    alert.setGraphic(null);
    alert.initOwner(ownerWindow);
    alert.showAndWait();
  }

  private ExceptionAlert() {}
}
