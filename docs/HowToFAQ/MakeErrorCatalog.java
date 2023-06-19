import java.util.*;
import java.io.*;
public class MakeErrorCatalog {

  public static void main(String ... args) {
    String template = args[0];
    List<String> ids = new LinkedList<>();
    Map<String,String> explanations = new HashMap<>();
    for (int i = 1; i < args.length; i++) {
     String file = args[i];
     try (BufferedReader br = new BufferedReader(new FileReader(file))) {
      String line = null;  
      String text = null;
      String errorid = null;
      boolean inblock = false;
      int number = 0;
      while ((line = br.readLine()) != null) {  
        number++;
        if (line.contains("Add(ErrorId")) {
          if (inblock) {
            System.out.println("SYNTAX ERROR LINE " + number + ": New errorid while still in text block");
            System.exit(1);
          }
          errorid = line.replace("Add(ErrorId.","").replaceAll(",.*","").trim();
          ids.add(errorid);
          if (errorid.length() == 0 || errorid.contains(" ")) {
            System.out.println("SYNTAX ERROR LINE " + number + ": Invalid errorid: " + errorid);
            System.exit(1);
          }
          continue;
        }
        if (line.contains("@\"")) {
          if (inblock) {
            System.out.println("SYNTAX ERROR LINE " + number + ": Start of block detected while in block");
            System.exit(1);
          }
          if (errorid == null) {
            System.out.println("SYNTAX ERROR LINE " + number + ": No errorid known at start of explanation block");
            System.exit(1);
          }
          inblock = true;
          text = "";
          continue;
        }
        if (line.startsWith("\"")) {
          if (!inblock) {
            System.out.println("SYNTAX ERROR LINE " + number + ": End of block detected while not in block");
            System.exit(1);
          }
          inblock = false;
          explanations.put(errorid,text.replaceAll("\"\"","\""));
          errorid = null;
          continue;
        }
        if (inblock) {
          text += line + "\n";
          continue;
        }
      } 
      if (inblock) {
        System.out.println("FAILURE - SYNTAX: ended file in block");
        System.exit(1);
      }
     } catch (Exception e) {
        System.out.println("EXCEPTION: " + e);
        e.printStackTrace(System.out);
        System.exit(1);
     }
    }

/*
    for (var s: ids) {
      System.out.println("ERRORID: " + s);
      System.out.println(explanations.get(s));
    }
*/
    String outname = template.replace("template","tmp");
    try (PrintStream fileout = new PrintStream(outname); BufferedReader br = new BufferedReader(new FileReader(template))) {
      String line = null;
      String errorid = null;
      boolean inblock = false;
      int number = 0;
      while ((line = br.readLine()) != null) {
        number++;
        if (line.startsWith("## **")) {
          int k = line.indexOf("{#");
          int kk = line.lastIndexOf("}");
          if (k == -1 || kk == -1) {
            System.out.println("SYNTAX ERROR IN TEMPLATE LINE " + number + ": no errorid");
            System.exit(1);
          }
          errorid = line.substring(k+2, kk);
          fileout.println(line);
          continue;
        }
        if (line.contains("INSERT-TEXT")) {
          var text = explanations.get(errorid);
          if (text != null) {
            fileout.print(text); // text already has trailing newline
          } else {
            fileout.println(line);
            System.out.println("Unknown errorid: " + errorid);
          }
        } else {
          fileout.println(line);
        }
      }
    } catch (Exception e) {
        System.out.println("EXCEPTION: " + e);
        e.printStackTrace(System.out);
        System.exit(1);
    }
    System.exit(0);
  }
}
