package tlc2.util;

import java.net.URL;
import java.net.URLClassLoader;
import java.util.Objects;

/**
 * URLClassLoader variant that applies child-first loading semantics for the
 * TLC code base.
 */
public final class ChildFirstClassLoader extends URLClassLoader {

    private static final String[] PARENT_FIRST_PREFIXES = {
            "java.",
            "javax.",
            "jdk.",
            "sun.",
            "com.sun.",
            "org.w3c.",
            "org.xml."
    };

    private static final String[] CHILD_FIRST_PREFIXES = {
            "tlc2.",
            "tla2sany.",
            "pcal.",
            "model.",
            "util.",
            "org.lamport."
    };

    public ChildFirstClassLoader(final URL[] urls, final ClassLoader parent) {
        super(Objects.requireNonNull(urls, "urls"), Objects.requireNonNull(parent, "parent"));
    }

    @Override
    protected Class<?> loadClass(final String name, final boolean resolve) throws ClassNotFoundException {
        synchronized (getClassLoadingLock(name)) {
            Class<?> clazz = findLoadedClass(name);
            if (clazz == null) {
                if (shouldLoadChildFirst(name)) {
                    try {
                        clazz = findClass(name);
                    } catch (final ClassNotFoundException ignore) {
                        // Fallback to parent when the class is not available via findClass.
                    }
                }
                if (clazz == null) {
                    return super.loadClass(name, resolve);
                }
            }
            if (resolve) {
                resolveClass(clazz);
            }
            return clazz;
        }
    }

    private static boolean shouldLoadChildFirst(final String className) {
        for (final String prefix : PARENT_FIRST_PREFIXES) {
            if (className.startsWith(prefix)) {
                return false;
            }
        }
        for (final String prefix : CHILD_FIRST_PREFIXES) {
            if (className.startsWith(prefix)) {
                return true;
            }
        }
        return false;
    }
}
