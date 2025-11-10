package tlc2.util;

import java.io.File;
import java.net.MalformedURLException;
import java.net.URL;
import java.util.ArrayList;
import java.util.List;

/** Utility for collecting URLs from the current {@code java.class.path}. */
public final class ClassPathCollector {

    private ClassPathCollector() {
        // Utility.
    }

    public static URL[] collect() {
        final String rawClassPath = System.getProperty("java.class.path", "");
        final String[] entries = rawClassPath.split(File.pathSeparator);
        final List<URL> urls = new ArrayList<>(entries.length);
        for (final String entry : entries) {
            if (entry == null || entry.isEmpty()) {
                continue;
            }
            final File candidate = new File(entry);
            if (!candidate.exists()) {
                continue;
            }
            try {
                urls.add(candidate.toURI().toURL());
            } catch (final MalformedURLException ignore) {
                // Skip entries that cannot be converted into a valid URL.
            }
        }
        return urls.toArray(new URL[0]);
    }
}
