package presentation.utils;

import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.time.format.DateTimeParseException;


public class DateUtil {

  private static final /*@ spec_public nullable @*/ String DATE_PATTERN = "dd/MM/yy";
  private static final /*@ spec_public nullable @*/ DateTimeFormatter DATE_FORMATER = DateTimeFormatter.ofPattern(DATE_PATTERN);


  public static String format(LocalDateTime date) {
    if (date != null) {
      return DATE_FORMATER.format(date);
    }
    return null;
  }

  public static LocalDateTime parse(String dateString) {
    try {
      return LocalDateTime.parse(dateString, DATE_FORMATER);
    } catch (DateTimeParseException e) {
      return null;
    }
  }

  private DateUtil() {}
}
