// This program inserts section numbers into a .md document (replacing
// any that are there). It also puts in the section numbers in
// cross-reference links.
// A heading line consists of: one or more #, a dotted section number,
// the section title, and the reference {#sec-name}
// A section cross-reference is: [Section 0](#sec-name)

import java.nio.file.*;
import java.util.*;
import java.io.*;
import java.util.regex.*;

public class Numbers {

  public static Pattern inc = Pattern.compile("\\{%\\s+include(_relative)?\\s+([\\w.\\d/_-]+)");
  public static Pattern sec = Pattern.compile("^[ \\t0-9\\.]*([#]+)\\h+(\\D|((\\d+\\.)+))");
  public static Pattern ref = Pattern.compile("\\{#([\\w-]+)\\}");
  public static Pattern cite = Pattern.compile("\\(#([\\w-]+)\\)");
  public static Pattern seccite = Pattern.compile("(\\[Section [\\d\\.]+\\])\\(#([\\w-]+)\\)");

  public static Set<String> cites = new HashSet<>();
  public static Map<String,String> labels = new HashMap<>();

  public static int[] counts = new int[100];
  public static int depth = 0;
  public static boolean replace = false;
  public static boolean verbose = false;

  public static void main(String[] args) {
    int i = 0;
    if (i < args.length && args[i].equals("-v")) { verbose = true; i++; }
    if (i < args.length && args[i].equals("-r")) { replace = true; i++; }
    process(args[i], false);
    if (replace) {
      depth = 0; counts = new int[100];
      process(args[i], true);
    }


    if (verbose) System.out.println("Number of cites: " + cites.size());
    //for (String s: cites) System.out.println("   " + s);
    if (verbose) System.out.println("Number of labels: " + labels.size());
    for (String s: cites) {
      if (!labels.containsKey(s)) System.out.println(" No label: " + s);
    }
}

public static String num() {
  String s = "";
  for (int k=0; k < depth; k++) s = s + counts[k] + '.';
  return s;
}

public static void process(String file, boolean replace) {
  if (verbose) System.out.println("Opening " + file);
  try (FileReader f = new FileReader(file);
       BufferedReader r = new BufferedReader(f)) {
    PrintWriter w = null;
    if (replace) w = new PrintWriter(new BufferedWriter(new FileWriter(file + ".tmp")));

    String line;
    while ((line = r.readLine()) != null) {
      String out = line;
      Matcher m = inc.matcher(line);
      if (m.find()) {
        if (replace) w.println(line);
        String rel = m.group(1);
        String newfile = m.group(2);
        if (newfile.endsWith(".md")) {
          String fn = rel == null ? "../_includes/" + newfile : newfile ;
          process(fn, replace);
        }
        continue;
      }
      m = sec.matcher(line);
      if (m.find() && m.start() == 0) {
        String hashes = m.group(1);
        String digits = m.group(3);
        int textpos = m.end(1);
        if (digits != null) textpos = m.end(3);
        int k = hashes.length();
        while (depth > k) counts[--depth] = 0;
        if (k > depth+1) System.out.println("Skipping a level");
        if (k > depth) ++depth;
        counts[depth-1]++;
        String n = num();
        if (digits != null && !n.equals(digits)) System.out.println("number mismatch " + digits + " vs. " + n);
        m = ref.matcher(line);
        if (m.find()) {
          String refname = m.group(1);
          if (verbose) System.out.println("    " + refname + " : " + n);
          labels.put(refname,n);
        }
        out = (hashes + " " + n + line.substring(textpos));
        if (verbose) {
          System.out.println(out);
        }
      }
      if (!replace) {
        m = cite.matcher(out);
        if (m.find()) {
          String s = m.group(1);
          cites.add(s);
        }
      } else {
        m = seccite.matcher(out);
        int q = -1;
        while (m.find(q+1)) {
          String s = m.group(1);
          String ref = m.group(2);
          String num = labels.get(ref);
          if (num == null) {
             System.out.println("No match for " + ref);
             break;
          } else {
             q = m.start();
             int e = m.end();
             String nn =  "[Section " + num.substring(0,num.length()-1) + "](#" + ref + ")";
             if (verbose) System.out.println(nn + " <== " + out.substring(q,e));
             out = out.substring(0,q) + nn + out.substring(e);
             m = seccite.matcher(out);
          }
        }
      }
      if (replace) w.println(out);
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
