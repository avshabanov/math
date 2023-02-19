#include <stdio.h>
#include <string.h>

static const char* g_elems[] = {
  "#include <stdio.h>\n#include <string.h>\n\nstatic const char* g_elems[] = {\n  \"",
  "\"\n};\n\nstatic inline void print_quoted(const char* v) {\n  for (; *v != 0; ++v) {\n    switch (*v) {\n    case '\\n': printf(\"\\\\n\"); break;\n    case '\\\\': printf(\"\\\\\\\\\"); break;\n    case '\\\"': printf(\"\\\\\\\"\"); break;\n    default: putchar(*v);\n    }\n  }\n}\n\nint main() {\n  printf(\"%s\", g_elems[0]);\n  print_quoted(g_elems[0]);\n  printf(\"\\\",\\n  \\\"\");\n  print_quoted(g_elems[1]);\n  puts(g_elems[1]);\n  return 0;\n}"
};

static inline void print_quoted(const char* v) {
  for (; *v != 0; ++v) {
    switch (*v) {
    case '\n': printf("\\n"); break;
    case '\\': printf("\\\\"); break;
    case '\"': printf("\\\""); break;
    default: putchar(*v);
    }
  }
}

int main() {
  printf("%s", g_elems[0]);
  print_quoted(g_elems[0]);
  printf("\",\n  \"");
  print_quoted(g_elems[1]);
  puts(g_elems[1]);
  return 0;
}
