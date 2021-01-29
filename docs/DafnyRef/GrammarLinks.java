
import java.nio.file.*;
import java.util.*;
import java.io.*;
import java.util.regex.*;

public class GrammarLinks {

  public static String grammarLabels = "<!--GS-->";
  public static String grammarLinks = "<!--GE-->";
  public static Pattern inc = Pattern.compile("\\{%\\h+include_relative\\h+([\\w.]+)");
  public static Pattern grammar = Pattern.compile("````grammar");
  public static Pattern grammarEnd = Pattern.compile("````");
  public static Pattern labels = Pattern.compile(grammarLabels);
  public static Pattern links = Pattern.compile(grammarLinks);
  public static Pattern head = Pattern.compile("\\h*([\\w\\d_-]+)(\\([^\\)]*\\))?\\h*=");
  public static Pattern ref = Pattern.compile("([\\(\\){}\\[\\]\\|\\h]|\"[^\"]+\")*([\\w\\d_!-]+)");

  public static boolean replace = false;
  public static boolean verbose = false;
  public static List<String> lines = new ArrayList<String>();
  public static HashSet<String> heads = new HashSet<String>();
  public static HashSet<String> refs = new HashSet<String>();
  public static HashSet<String> allheads = new HashSet<String>();
  public static HashSet<String> allrefs = new HashSet<String>();
  public static HashSet<String> no = new HashSet<>();
  static {
    no.add("true");
    no.add("false");
    no.add("go");
    no.add("body-less");
  }

  public static void main(String[] args) {
    int i = 0;
    if (i < args.length && args[i].equals("-v")) { verbose = true; i++; }
    if (i < args.length && args[i].equals("-r")) { replace = true; i++; }
    process(args[i], false);
    for (String rr: allheads) {
      if (!allrefs.contains(rr)) System.out.println("UNUSED HEAD " + rr);
    }
    for (String rr: allrefs) {
      if (!allheads.contains(rr)) System.out.println("ORPHAN REF " + rr);
    }

    if (replace) {
      process(args[i], true);
    }
}

public static void process(String file, boolean replace) {
  if (verbose) System.out.println("Opening " + file);
  try (FileReader f = new FileReader(file);
       BufferedReader r = new BufferedReader(f)) {
    PrintWriter w = null;
    if (replace) w = new PrintWriter(new BufferedWriter(new FileWriter(file + ".tmp")));

    String line;
    outer: while ((line = r.readLine()) != null) {
      String out = line;
      Matcher m = inc.matcher(line);
      if (m.find()) {
        if (replace) w.println(line);
        String newfile = m.group(1);
        if (newfile.endsWith(".md")) process(newfile, replace);
        continue;
      }
      m = links.matcher(line);
      if (m.find()) continue;
      m = grammar.matcher(line);
      if (m.find() && m.start() == 0) {
         lines.clear();
         heads.clear();
         refs.clear();
         lines.add(line);
         String h = " ";
         while ((line = r.readLine()) != null) {
           lines.add(line);
           Matcher mm = grammarEnd.matcher(line);
           if (mm.find() && mm.start() == 0) break;
           int k = 0;
           mm = head.matcher(line);
           if (mm.find() && mm.start() == 0) {
              h = mm.group(1);
              if (verbose) System.out.println("HEAD: " + h);
              heads.add(h);
              k = mm.end();
           }
           int comment = line.indexOf("//");
           //if ('A' <= h.charAt(0) && h.charAt(0) <= 'Z') {
           {
             mm = ref.matcher(line);
             while (mm.find(k)) {
               if (comment >= 0 && mm.start(2) > comment) break;
               String rf = mm.group(2);
               int p = mm.start(2);
               k = mm.end(2);
               if (p > 0 && line.charAt(p-1) == '"' && line.charAt(k) == '"') break;
               if (verbose) System.out.println("REF: " + rf);
               if (!no.contains(rf)) refs.add(rf);
               if (k < line.length() && line.charAt(k) == '(') {
                   int kk = line.indexOf(')',k);
                   if (kk > k) k = kk;
                   boolean skipping = kk == -1;
                   while (kk == -1) {
                       line = r.readLine();
                       if (line == null) break outer;
                       kk = line.indexOf(')');
                   }
                   if (skipping) break;
               }
             }
             allrefs.addAll(refs);
           }
         }
         allheads.addAll(heads);
         if (line == null) {
           System.out.println("No end to grammar block found");
           System.exit(1);
         }
         String lab = grammarLabels;
         for (String hh: heads) {
           lab += " {#G-" + hh + "}";
         }
         if (verbose) System.out.println(lab);
         if (replace) w.println(lab);
         for (String s: lines) {
           if (replace) w.println(s);
         }
         String links = grammarLinks;
         for (String rr: refs) {
           links += " ["+rr+"](#G-"+rr+")";
         }
         if (verbose) System.out.println(links);
         if (replace) w.println(links);
      } else {
        if (replace) w.println(out);
      }
    }
    if (w != null) {
      w.close();
      Path a = FileSystems.getDefault().getPath(file + ".tmp");
      Path b = FileSystems.getDefault().getPath(file);
      Files.move(a,b, StandardCopyOption.REPLACE_EXISTING);
    }
  } catch (Exception e) {
    System.out.println(e.getMessage());
  }
  if (verbose) System.out.println("Closing " + file);
}

}
