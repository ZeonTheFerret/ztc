#define _POSIX_C_SOURCE 200809L
#define _DEFAULT_SOURCE

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <stdbool.h>
#include <ctype.h>
#include <stdarg.h>
#include <errno.h>
#include <unistd.h>
#include <sys/wait.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <fcntl.h>
#include <signal.h>
#include <math.h>
#include <stdint.h>

#include <openssl/sha.h>

#define ZTC_VERSION "0.1"

static void *xmalloc(size_t n) {
    void *p = malloc(n);
    if (!p) {
        fprintf(stderr, "E: out of memory (requested %zu bytes)\n", n);
        exit(EXIT_FAILURE);
    }
    return p;
}

static char *xstrdup(const char *s) {
    char *p = strdup(s);
    if (!p) {
        fprintf(stderr, "E: out of memory (strdup)\n");
        exit(EXIT_FAILURE);
    }
    return p;
}

static char *xstrndup(const char *s, size_t n) {
    char *p = strndup(s, n);
    if (!p) {
        fprintf(stderr, "E: out of memory (strndup)\n");
        exit(EXIT_FAILURE);
    }
    return p;
}

static void *xrealloc(void *p, size_t n) {
    void *q = realloc(p, n);
    if (!q) {
        fprintf(stderr, "E: out of memory (realloc %zu)\n", n);
        exit(EXIT_FAILURE);
    }
    return q;
}

static void zt_warn(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    fputs("W: ", stderr);
    vfprintf(stderr, fmt, ap);
    fputc('\n', stderr);
    va_end(ap);
}

static void zt_error(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    fputs("E: ", stderr);
    vfprintf(stderr, fmt, ap);
    fputc('\n', stderr);
    va_end(ap);
}

static int levenshtein(const char *a, const char *b) {
    size_t la = strlen(a), lb = strlen(b);
    if (la == 0) return (int)lb;
    if (lb == 0) return (int)la;
    int *prev = xmalloc(sizeof(int) * (lb + 1));
    int *curr = xmalloc(sizeof(int) * (lb + 1));
    for (size_t j = 0; j <= lb; j++) prev[j] = (int)j;
    for (size_t i = 1; i <= la; i++) {
        curr[0] = (int)i;
        for (size_t j = 1; j <= lb; j++) {
            int cost = (tolower((unsigned char)a[i-1]) ==
                        tolower((unsigned char)b[j-1])) ? 0 : 1;
            int del = prev[j] + 1;
            int ins = curr[j-1] + 1;
            int sub = prev[j-1] + cost;
            int m = del < ins ? del : ins;
            curr[j] = m < sub ? m : sub;
        }
        int *tmp = prev; prev = curr; curr = tmp;
    }
    int d = prev[lb];
    free(prev);
    free(curr);
    return d;
}

static const char *suggest_keyword(const char *word) {
    static const char *keywords[] = {
        "ztsl.start", "ztsl.end",
        "ztslo.start", "ztslo.end",
        "define", "variable", "as",
        "if", "then", "else", "or", "is", "not",
        "func", "sys.exec", "text.show",
        "shell", "exec",
        "empty", "file", "returns",
        "read_file", "delete_file", "create_file",
        "write_on_file", "append_file", "ccompat",
        "calculate",
        NULL
    };
    size_t wlen = 0;
    while (word[wlen] && !isspace((unsigned char)word[wlen]) &&
           word[wlen] != '"' && word[wlen] != '(') {
        wlen++;
    }
    if (wlen == 0) return NULL;
    char *first = xstrndup(word, wlen);
    int best_d = 1000;
    const char *best = NULL;
    for (size_t i = 0; keywords[i]; i++) {
        int d = levenshtein(first, keywords[i]);
        if (d < best_d) { best_d = d; best = keywords[i]; }
    }
    free(first);
    if (best_d <= 2) return best;
    return NULL;
}

static char *str_trim(char *s) {
    if (!s) return NULL;
    while (*s && isspace((unsigned char)*s)) s++;
    if (*s == '\0') return s;
    char *end = s + strlen(s) - 1;
    while (end > s && isspace((unsigned char)*end)) {
        *end = '\0';
        end--;
    }
    return s;
}

static char *str_trim_dup(const char *s) {
    char *dup = xstrdup(s);
    char *t = str_trim(dup);
    if (t != dup) memmove(dup, t, strlen(t) + 1);
    return dup;
}

typedef struct {
    char  *data;
    size_t len;
    size_t cap;
} dstring;

static void dstr_init(dstring *d) {
    d->cap = 64;
    d->len = 0;
    d->data = xmalloc(d->cap);
    d->data[0] = '\0';
}

static void dstr_free(dstring *d) {
    free(d->data);
    d->data = NULL;
    d->len = d->cap = 0;
}

static void dstr_reserve(dstring *d, size_t need) {
    if (d->cap >= need + 1) return;
    while (d->cap < need + 1) d->cap *= 2;
    d->data = xrealloc(d->data, d->cap);
}

static void dstr_append(dstring *d, const char *s, size_t n) {
    dstr_reserve(d, d->len + n);
    memcpy(d->data + d->len, s, n);
    d->len += n;
    d->data[d->len] = '\0';
}

static void dstr_append_cstr(dstring *d, const char *s) {
    dstr_append(d, s, strlen(s));
}

static void dstr_append_char(dstring *d, char c) {
    dstr_reserve(d, d->len + 1);
    d->data[d->len++] = c;
    d->data[d->len] = '\0';
}

typedef struct {
    char **lines;
    size_t count;
} LineBuf;

static void linebuf_init(LineBuf *lb) {
    lb->lines = NULL;
    lb->count = 0;
}

static void linebuf_free(LineBuf *lb) {
    for (size_t i = 0; i < lb->count; i++) {
        
        if (lb->lines[i]) free(lb->lines[i]);
    }
    free(lb->lines);
    lb->lines = NULL;
    lb->count = 0;
}

static void linebuf_push(LineBuf *lb, char *line) {
    
    lb->lines = xrealloc(lb->lines, sizeof(char *) * (lb->count + 1));
    lb->lines[lb->count++] = line;
}

static char *read_file(const char *path) {
    FILE *f = fopen(path, "rb");
    if (!f) return NULL;
    if (fseek(f, 0, SEEK_END) != 0) { fclose(f); return NULL; }
    long sz = ftell(f);
    if (sz < 0) { fclose(f); return NULL; }
    rewind(f);
    char *buf = xmalloc((size_t)sz + 1);
    size_t got = fread(buf, 1, (size_t)sz, f);
    fclose(f);
    buf[got] = '\0';
    return buf;
}

static void file_to_lines(const char *content, LineBuf *lb) {
    bool in_code_fence = false;
    const char *p = content;
    dstring cur;
    dstr_init(&cur);

    while (*p) {
        
        if (!in_code_fence && *p == '#') {
            
            while (*p && *p != '\n') p++;
            continue;
        }

        
        if (*p == '`' && p[1] == '`' && p[2] == '`') {
            in_code_fence = !in_code_fence;
            
            dstr_append_cstr(&cur, "```");
            p += 3;
            continue;
        }

        if (*p == '\n') {
            
            char *line = str_trim_dup(cur.data);
            if (line[0] != '\0') linebuf_push(lb, line);
            else free(line);
            dstr_free(&cur);
            dstr_init(&cur);
            p++;
            continue;
        }

        dstr_append_char(&cur, *p);
        p++;
    }

    
    if (cur.len > 0) {
        char *line = str_trim_dup(cur.data);
        if (line[0] != '\0') linebuf_push(lb, line);
        else free(line);
    }
    dstr_free(&cur);
}

typedef enum {
    K_DEFINE,
    K_IF,
    K_EXEC,
    K_SHOW,
    K_DELETE,
    K_CREATE,
    K_WRITE,
    K_APPEND,
    K_CCOMPAT,
    K_FLOATCALC,
} StmtKind;

typedef enum {
    COND_EQ,
    COND_EMPTYFILE,
} CondKind;

typedef enum {
    SUBJ_VAR,
    SUBJ_READFILE,
} CondSubj;

typedef struct Stmt Stmt;

typedef struct {
    

    CondKind kind;
    CondSubj subj;
    char    *var;           
    char    *path;          
    bool     is_is;        
    char   **values;       
    size_t   nvalues;
    Stmt    *then_branch;  
    Stmt    *else_branch;
} Cond;

struct Stmt {
    StmtKind  kind;
    Stmt     *next;
    union {
        struct { char *name; char *value; } define;
        Cond     cond;
        struct { bool is_shell; char *code; } exec;
        struct { char *code; } show;
        struct { char *path; } delfile;
        struct { char *path; } mkfile;
        struct { char *path; char *code; } writefile;
        struct { char *code; } ccompat;
        struct { int width; char op; char *lhs_raw; char *rhs_raw; char *varname; } floatcalc;
    };
};

typedef struct Func {
    char   *name;
    Stmt   *body;
    struct Func *next;
} Func;

typedef struct Var {
    char   *name;
    char   *value;
    struct Var *next;
} Var;

typedef struct {
    Func *funcs;
    Var  *vars;
    bool  inline_ztslo_used;
} Program;

typedef struct {
    LineBuf *lb;
    size_t   pos;
    bool     error;
    char    *err_msg;
} Parser;

static void parse_error(Parser *p, const char *msg) {
    if (!p->error) {
        p->error = true;
        p->err_msg = xstrdup(msg);
    }
}

static const char *peek(Parser *p) {
    while (p->pos < p->lb->count) {
        const char *line = p->lb->lines[p->pos];
        if (line[0] == '\0') { p->pos++; continue; }
        return line;
    }
    return NULL;
}

static char *consume(Parser *p) {
    while (p->pos < p->lb->count) {
        char *line = p->lb->lines[p->pos];
        p->pos++;
        if (line[0] == '\0') { free(line); continue; }
        

        p->lb->lines[p->pos - 1] = NULL;
        return line;
    }
    return NULL;
}

static bool starts_with_kw(const char *line, const char *kw) {
    size_t n = strlen(kw);
    if (strlen(line) < n) return false;
    for (size_t i = 0; i < n; i++) {
        if (tolower((unsigned char)line[i]) != tolower((unsigned char)kw[i]))
            return false;
    }
    char c = line[n];
    if (c == '\0' || isspace((unsigned char)c) || c == ';') return true;
    return false;
}

static char *extract_quoted(const char *s, const char **endp) {
    while (*s && isspace((unsigned char)*s)) s++;
    if (*s != '"') { if (endp) *endp = s; return NULL; }
    s++;
    const char *start = s;
    while (*s && *s != '"') {
        if (*s == '\\' && s[1]) s++;
        s++;
    }
    if (*s != '"') { if (endp) *endp = s; return NULL; }
    char *out = xstrndup(start, (size_t)(s - start));
    s++;
    if (endp) *endp = s;
    return out;
}

static void stmt_free(Stmt *s) {
    while (s) {
        Stmt *next = s->next;
        switch (s->kind) {
            case K_DEFINE:
                free(s->define.name);
                free(s->define.value);
                break;
            case K_IF:
                free(s->cond.var);
                free(s->cond.path);
                for (size_t i = 0; i < s->cond.nvalues; i++)
                    free(s->cond.values[i]);
                free(s->cond.values);
                stmt_free(s->cond.then_branch);
                stmt_free(s->cond.else_branch);
                break;
            case K_EXEC:
                free(s->exec.code);
                break;
            case K_SHOW:
                free(s->show.code);
                break;
            case K_DELETE:
                free(s->delfile.path);
                break;
            case K_CREATE:
                free(s->mkfile.path);
                break;
            case K_WRITE:
            case K_APPEND:
                free(s->writefile.path);
                free(s->writefile.code);
                break;
            case K_CCOMPAT:
                free(s->ccompat.code);
                break;
            case K_FLOATCALC:
                free(s->floatcalc.lhs_raw);
                free(s->floatcalc.rhs_raw);
                free(s->floatcalc.varname);
                break;
        }
        free(s);
        s = next;
    }
}

static void func_free(Func *f) {
    while (f) {
        Func *next = f->next;
        free(f->name);
        stmt_free(f->body);
        free(f);
        f = next;
    }
}

static void var_free(Var *v) {
    while (v) {
        Var *next = v->next;
        free(v->name);
        free(v->value);
        free(v);
        v = next;
    }
}

static char *parse_code_block(Parser *p, bool *is_shell, bool allow_tags) {
    char *line = consume(p);
    if (!line) {
        parse_error(p, "expected code block, got EOF");
        return NULL;
    }
    
    if (strncmp(line, "```", 3) != 0) {
        parse_error(p, "expected ``` to open code block");
        free(line);
        return NULL;
    }
    const char *tag = line + 3;
    while (*tag && isspace((unsigned char)*tag)) tag++;
    if (tag[0] == '\0') {
        
        *is_shell = true;
    } else if (!allow_tags) {
        
        zt_error("text.show does not accept shell/exec tags; use bare ```");
        free(line);
        parse_error(p, "text.show with forbidden tag");
        return NULL;
    } else if (strcmp(tag, "shell") == 0) {
        *is_shell = true;
    } else if (strcmp(tag, "exec") == 0) {
        *is_shell = false;
    } else {
        zt_error("unknown code fence tag '%s' (expected shell/exec)", tag);
        free(line);
        parse_error(p, "unknown code fence tag");
        return NULL;
    }
    free(line);

    dstring code;
    dstr_init(&code);

    while (p->pos < p->lb->count) {
        char *l = p->lb->lines[p->pos];
        if (strcmp(l, "```") == 0) {
            
            p->lb->lines[p->pos] = NULL;
            p->pos++;
            free(l);
            return code.data;
        }
        dstr_append_cstr(&code, l);
        dstr_append_char(&code, '\n');
        p->pos++;
    }

    dstr_free(&code);
    parse_error(p, "unterminated code block (missing closing ```)");
    return NULL;
}

static char *parse_raw_block(Parser *p) {
    char *line = consume(p);
    if (!line) {
        parse_error(p, "expected code block, got EOF");
        return NULL;
    }
    if (strncmp(line, "```", 3) != 0) {
        parse_error(p, "expected ``` to open code block");
        free(line);
        return NULL;
    }
    free(line);

    dstring code;
    dstr_init(&code);

    while (p->pos < p->lb->count) {
        char *l = p->lb->lines[p->pos];
        if (strcmp(l, "```") == 0) {
            p->lb->lines[p->pos] = NULL;
            p->pos++;
            free(l);
            return code.data;
        }
        dstr_append_cstr(&code, l);
        dstr_append_char(&code, '\n');
        p->pos++;
    }

    dstr_free(&code);
    parse_error(p, "unterminated code block (missing closing ```)");
    return NULL;
}

static Stmt *parse_stmt(Parser *p);
static Stmt *parse_stmt_list(Parser *p, const char *terminator);

static Stmt *parse_define(Parser *p, char *first_line) {
    (void)first_line;
    char *line = consume(p);
    if (!line) { parse_error(p, "EOF in define"); return NULL; }

    

    char *save = line;

    char *cursor = save;
    
    while (*cursor && isspace((unsigned char)*cursor)) cursor++;
    while (*cursor && !isspace((unsigned char)*cursor)) cursor++;
    while (*cursor && isspace((unsigned char)*cursor)) cursor++;
    
    char *var_kw = cursor;
    while (*cursor && !isspace((unsigned char)*cursor)) cursor++;
    if (*cursor) { *cursor++ = '\0'; }
    while (*cursor && isspace((unsigned char)*cursor)) cursor++;
    if (var_kw[0] == '\0' || strcasecmp(var_kw, "variable") != 0) {
        parse_error(p, "expected 'variable' after 'define'");
        free(save);
        return NULL;
    }
    
    char *name = cursor;
    while (*cursor && !isspace((unsigned char)*cursor)) cursor++;
    if (*cursor) *cursor++ = '\0';
    while (*cursor && isspace((unsigned char)*cursor)) cursor++;
    if (name[0] == '\0') {
        parse_error(p, "expected variable name");
        free(save);
        return NULL;
    }
    
    char *as_kw = cursor;
    while (*cursor && !isspace((unsigned char)*cursor)) cursor++;
    if (*cursor) *cursor++ = '\0';
    while (*cursor && isspace((unsigned char)*cursor)) cursor++;
    if (as_kw[0] == '\0' || strcasecmp(as_kw, "as") != 0) {
        parse_error(p, "expected 'as' after variable name");
        free(save);
        return NULL;
    }
    
    const char *endp = NULL;
    char *value = extract_quoted(cursor, &endp);
    if (!value) {
        parse_error(p, "expected quoted value after 'as'");
        free(save);
        return NULL;
    }
    
    char *name_copy = xstrdup(name);
    free(save);

    Stmt *s = xmalloc(sizeof(Stmt));
    memset(s, 0, sizeof(*s));
    s->kind = K_DEFINE;
    s->define.name  = name_copy;
    s->define.value = value;
    return s;
}

static bool match_word_boundary(const char *s, const char *word, size_t wlen) {
    if (strncasecmp(s, word, wlen) != 0) return false;
    char c = s[wlen];
    return (c == '\0' || isspace((unsigned char)c) || c == ';');
}

static bool match_float_calc_kw(const char *line, int *width_out, size_t *len_out) {
    if (strncasecmp(line, "float", 5) != 0) return false;
    const char *p = line + 5;
    const char *dstart = p;
    while (isdigit((unsigned char)*p)) p++;
    if (p == dstart) return false;
    int width = atoi(dstart);
    if (strncasecmp(p, "_calculate", 10) != 0) return false;
    const char *after = p + 10;
    if (!(*after == '\0' || isspace((unsigned char)*after) || *after == ';'))
        return false;
    *width_out = width;
    *len_out = (size_t)(after - line);
    return true;
}

static bool reject_if_misplaced_statement(Parser *p, const char *line) {
    int width; size_t kwlen;
    if (match_float_calc_kw(line, &width, &kwlen)) {
        zt_error("'floatNN_calculate' is a statement and must be inside "
                "a func \"name\" { ... } body, not here: '%s'", line);
        parse_error(p, "floatNN_calculate outside a func body");
        return true;
    }

    if (starts_with_kw(line, "define")) {
        zt_error("'define' must be inside a func \"name\" { ... } body "
                "or a ztslo.start/ztslo.end block, not here: '%s'", line);
        parse_error(p, "define outside a func body or ztslo block");
        return true;
    }

    static const char *stmt_keywords[] = {
        "if", "sys.exec", "text.show",
        "delete_file", "create_file",
        "write_on_file", "append_file",
        "ccompat",
        NULL
    };
    for (size_t i = 0; stmt_keywords[i]; i++) {
        if (starts_with_kw(line, stmt_keywords[i])) {
            zt_error("'%s' is a statement and must be inside a func \"name\" "
                    "{ ... } body, not here: '%s'", stmt_keywords[i], line);
            parse_error(p, "statement outside a func body");
            return true;
        }
    }
    return false;
}

static Stmt *parse_if(Parser *p) {
    char *line = consume(p);
    if (!line) { parse_error(p, "EOF in if"); return NULL; }

    
    char *s = line;
    while (*s && isspace((unsigned char)*s)) s++;
    s += 2;  
    while (*s && isspace((unsigned char)*s)) s++;

    
    CondSubj subj = SUBJ_VAR;
    char *var = NULL;
    char *fpath = NULL;

    if (match_word_boundary(s, "read_file", 9)) {
        s += 9;
        while (*s && isspace((unsigned char)*s)) s++;
        const char *endp = NULL;
        fpath = extract_quoted(s, &endp);
        if (!fpath) {
            parse_error(p, "expected quoted path after 'read_file'");
            free(line);
            return NULL;
        }
        subj = SUBJ_READFILE;
        s = (char *)endp;
        while (*s && isspace((unsigned char)*s)) s++;
    } else {
        char *var_start = s;
        while (*s && !isspace((unsigned char)*s)) s++;
        if (*s == '\0') {
            parse_error(p, "expected operator in if");
            free(line);
            return NULL;
        }
        *s++ = '\0';
        var = xstrdup(var_start);
        while (*s && isspace((unsigned char)*s)) s++;
    }

    
    bool is_is;
    CondKind ckind = COND_EQ;
    char **values = NULL;
    size_t nvalues = 0, cap = 0;
    bool seen_then = false;

    if (subj == SUBJ_VAR && match_word_boundary(s, "is not an empty file", 21)) {
        ckind = COND_EMPTYFILE;
        is_is = false;
        s += 21;
    } else if (subj == SUBJ_VAR && match_word_boundary(s, "is an empty file", 16)) {
        ckind = COND_EMPTYFILE;
        is_is = true;
        s += 16;
    } else if (strncasecmp(s, "is not", 6) == 0) {
        is_is = false;
        s += 6;
    } else if (strncasecmp(s, "returns", 7) == 0 &&
               (s[7] == '\0' || isspace((unsigned char)s[7]))) {
        is_is = true;
        s += 7;
    } else if (strncasecmp(s, "is", 2) == 0) {
        is_is = true;
        s += 2;
    } else if (strncmp(s, "=!", 2) == 0) {
        is_is = false;
        s += 2;
    } else if (strncmp(s, "!=", 2) == 0) {
        is_is = false;
        s += 2;
    } else {
        parse_error(p, "expected 'is', 'is not', 'returns', '=!' or '!=' in if");
        free(line);
        free(var);
        free(fpath);
        return NULL;
    }
    while (*s && isspace((unsigned char)*s)) s++;

    if (ckind == COND_EMPTYFILE) {
        
        if (strncasecmp(s, "then", 4) == 0 &&
            (s[4] == '\0' || isspace((unsigned char)s[4]) || s[4] == ';')) {
            s += 4;
            while (*s && (isspace((unsigned char)*s) || *s == ';')) s++;
            seen_then = true;
        }
        free(line);
        goto if_build;
    }

    

    while (*s) {
        if (*s == '"') {
            const char *endp = NULL;
            char *v = extract_quoted(s, &endp);
            if (!v) {
                parse_error(p, "bad quoted value in if");
                free(line);
                free(var);
                free(fpath);
                var = NULL;
                fpath = NULL;
                goto if_fail;
            }
            if (nvalues == cap) {
                cap = cap ? cap * 2 : 4;
                values = xrealloc(values, sizeof(char *) * (cap + 1));
            }
            values[nvalues++] = v;
            values[nvalues] = NULL;
            s = (char *)endp;
        } else {
            
            char *start = s;
            while (*s && !isspace((unsigned char)*s)) s++;
            char saved = *s;
            *s = '\0';
            char *v;
            if (strcasecmp(start, "empty") == 0) {
                
                v = xstrdup("");
            } else {
                v = xstrdup(start);
            }
            *s = saved;
            if (nvalues == cap) {
                cap = cap ? cap * 2 : 4;
                values = xrealloc(values, sizeof(char *) * (cap + 1));
            }
            values[nvalues++] = v;
            values[nvalues] = NULL;
        }
        while (*s && isspace((unsigned char)*s)) s++;

        
        if (strncasecmp(s, "or", 2) == 0 &&
            (s[2] == '\0' || isspace((unsigned char)s[2]))) {
            s += 2;
            while (*s && isspace((unsigned char)*s)) s++;
            continue;
        }
        
        if (strncasecmp(s, "then", 4) == 0 &&
            (s[4] == '\0' || isspace((unsigned char)s[4]) || s[4] == ';')) {
            s += 4;
            while (*s && (isspace((unsigned char)*s) || *s == ';')) s++;
            seen_then = true;
            break;
        }
        
        if (*s == '\0') break;
    }

    free(line);

if_build:
    
    if (!seen_then) {
        const char *next = peek(p);
        if (next && starts_with_kw(next, "then")) {
            char *nl = consume(p);
            free(nl);
        }
    }

    Stmt *stmt = xmalloc(sizeof(Stmt));
    memset(stmt, 0, sizeof(*stmt));
    stmt->kind = K_IF;
    stmt->cond.kind    = ckind;
    stmt->cond.subj    = subj;
    stmt->cond.var     = var;  
    var = NULL;
    stmt->cond.path    = fpath;
    fpath = NULL;
    stmt->cond.is_is   = is_is;
    stmt->cond.values  = values;
    stmt->cond.nvalues  = nvalues;
    stmt->cond.then_branch = NULL;
    stmt->cond.else_branch = NULL;

    
    stmt->cond.then_branch = parse_stmt_list(p, "else");
    if (p->error) {
        stmt_free(stmt);
        return NULL;
    }

    
    const char *nx = peek(p);
    if (nx && starts_with_kw(nx, "else")) {
        char *el = consume(p);
        free(el);
        stmt->cond.else_branch = parse_stmt_list(p, NULL);
        if (p->error) {
            stmt_free(stmt);
            return NULL;
        }
    }

    
    const char *maybe_endif = peek(p);
    if (maybe_endif && starts_with_kw(maybe_endif, "endif")) {
        char *ei = consume(p);
        free(ei);
    }

    return stmt;

if_fail:
    free(var);
    free(fpath);
    for (size_t i = 0; i < nvalues; i++) free(values[i]);
    free(values);
    return NULL;
}

static Stmt *parse_stmt_list(Parser *p, const char *terminator) {
    Stmt *head = NULL, *tail = NULL;
    while (true) {
        const char *line = peek(p);
        if (!line) break;

        
        if (terminator && starts_with_kw(line, terminator)) break;

        
        if (line[0] == '}') break;

        
        if (starts_with_kw(line, "endif")) break;

        
        if (starts_with_kw(line, "ztsl.end") || starts_with_kw(line, "zstl.end"))
            break;

        if (starts_with_kw(line, "ztslo.end") || starts_with_kw(line, "zstlo.end")) break;

        Stmt *s = parse_stmt(p);
        if (!s) {
            if (p->error) {
                stmt_free(head);
                return NULL;
            }
            continue;
        }
        if (!head) {
            head = tail = s;
        } else {
            tail->next = s;
            tail = s;
        }
    }
    return head;
}

static Stmt *parse_stmt(Parser *p) {
    const char *line = peek(p);
    if (!line) return NULL;

    
    if (starts_with_kw(line, "define")) {
        return parse_define(p, NULL);
    }
    
    if (starts_with_kw(line, "if")) {
        return parse_if(p);
    }
    
    if (starts_with_kw(line, "sys.exec")) {
        char *l = consume(p);
        free(l);
        bool is_shell;
        char *code = parse_code_block(p, &is_shell, true);
        if (!code) return NULL;
        Stmt *s = xmalloc(sizeof(Stmt));
        memset(s, 0, sizeof(*s));
        s->kind = K_EXEC;
        s->exec.is_shell = is_shell;
        s->exec.code = code;
        return s;
    }
    
    if (starts_with_kw(line, "text.show")) {
        char *l = consume(p);
        free(l);
        bool is_shell;
        char *code = parse_code_block(p, &is_shell, false);
        if (!code) return NULL;
        Stmt *s = xmalloc(sizeof(Stmt));
        memset(s, 0, sizeof(*s));
        s->kind = K_SHOW;
        s->show.code = code;
        return s;
    }
    
    if (starts_with_kw(line, "delete_file") || starts_with_kw(line, "create_file")) {
        bool is_delete = starts_with_kw(line, "delete_file");
        char *l = consume(p);
        const char *cursor = l + (is_delete ? 11 : 11);
        while (*cursor && isspace((unsigned char)*cursor)) cursor++;
        const char *endp = NULL;
        char *path = extract_quoted(cursor, &endp);
        free(l);
        if (!path) {
            parse_error(p, is_delete ? "expected quoted path after 'delete_file'"
                                      : "expected quoted path after 'create_file'");
            return NULL;
        }
        Stmt *s = xmalloc(sizeof(Stmt));
        memset(s, 0, sizeof(*s));
        if (is_delete) {
            s->kind = K_DELETE;
            s->delfile.path = path;
        } else {
            s->kind = K_CREATE;
            s->mkfile.path = path;
        }
        return s;
    }
    
    if (starts_with_kw(line, "write_on_file") || starts_with_kw(line, "append_file")) {
        bool is_write = starts_with_kw(line, "write_on_file");
        char *l = consume(p);
        const char *cursor = l + (is_write ? 13 : 11);
        while (*cursor && isspace((unsigned char)*cursor)) cursor++;
        const char *endp = NULL;
        char *path = extract_quoted(cursor, &endp);
        free(l);
        if (!path) {
            parse_error(p, is_write ? "expected quoted path after 'write_on_file'"
                                     : "expected quoted path after 'append_file'");
            return NULL;
        }
        char *code = parse_raw_block(p);
        if (!code) { free(path); return NULL; }
        Stmt *s = xmalloc(sizeof(Stmt));
        memset(s, 0, sizeof(*s));
        s->kind = is_write ? K_WRITE : K_APPEND;
        s->writefile.path = path;
        s->writefile.code = code;
        return s;
    }
    {
        int width; size_t kwlen;
        if (match_float_calc_kw(line, &width, &kwlen)) {
            if (width != 32 && width != 42 && width != 64 &&
                width != 76 && width != 128) {
                zt_error("unsupported float width '%d' "
                        "(expected 32, 42, 64, 76 or 128)", width);
                char *l = consume(p);
                free(l);
                parse_error(p, "unsupported float width");
                return NULL;
            }
            char *l = consume(p);
            const char *cursor = l + kwlen;
            while (*cursor && isspace((unsigned char)*cursor)) cursor++;

            const char *start = cursor;
            while (*cursor && !isspace((unsigned char)*cursor)) cursor++;
            if (cursor == start) {
                parse_error(p, "expected left operand in float calculation");
                free(l);
                return NULL;
            }
            char *lhs = xstrndup(start, (size_t)(cursor - start));
            while (*cursor && isspace((unsigned char)*cursor)) cursor++;

            char op = *cursor;
            if (op != '+' && op != '-' && op != '*' && op != '/') {
                zt_error("expected +, -, * or / in float calculation");
                free(lhs);
                free(l);
                parse_error(p, "bad operator in float calculation");
                return NULL;
            }
            cursor++;
            while (*cursor && isspace((unsigned char)*cursor)) cursor++;

            start = cursor;
            while (*cursor && !isspace((unsigned char)*cursor)) cursor++;
            if (cursor == start) {
                parse_error(p, "expected right operand in float calculation");
                free(lhs);
                free(l);
                return NULL;
            }
            char *rhs = xstrndup(start, (size_t)(cursor - start));
            while (*cursor && isspace((unsigned char)*cursor)) cursor++;

            if (!match_word_boundary(cursor, "as", 2)) {
                parse_error(p, "expected 'as' in float calculation");
                free(lhs);
                free(rhs);
                free(l);
                return NULL;
            }
            cursor += 2;
            while (*cursor && isspace((unsigned char)*cursor)) cursor++;

            if (!match_word_boundary(cursor, "variable", 8)) {
                parse_error(p, "expected 'variable' in float calculation");
                free(lhs);
                free(rhs);
                free(l);
                return NULL;
            }
            cursor += 8;
            while (*cursor && isspace((unsigned char)*cursor)) cursor++;

            const char *endp = NULL;
            char *varname = extract_quoted(cursor, &endp);
            free(l);
            if (!varname) {
                parse_error(p, "expected quoted variable name after 'variable'");
                free(lhs);
                free(rhs);
                return NULL;
            }

            Stmt *s = xmalloc(sizeof(Stmt));
            memset(s, 0, sizeof(*s));
            s->kind = K_FLOATCALC;
            s->floatcalc.width  = width;
            s->floatcalc.op     = op;
            s->floatcalc.lhs_raw = lhs;
            s->floatcalc.rhs_raw = rhs;
            s->floatcalc.varname = varname;
            return s;
        }
    }
    
    if (starts_with_kw(line, "ccompat")) {
        char *l = consume(p);
        free(l);
        char *code = parse_raw_block(p);
        if (!code) return NULL;
        Stmt *s = xmalloc(sizeof(Stmt));
        memset(s, 0, sizeof(*s));
        s->kind = K_CCOMPAT;
        s->ccompat.code = code;
        return s;
    }

    
    char *l = consume(p);
    if (l) {
        const char *sug = suggest_keyword(l);
        if (sug) {
            zt_error("unknown line: '%s' (did you mean '%s'?)", l, sug);
            free(l);
            parse_error(p, "unknown line with suggestion");
            return NULL;
        }
        zt_warn("skipping unknown line: %s", l);
        free(l);
    }
    return NULL;
}

static Func *parse_func(Parser *p) {
    char *line = consume(p);
    if (!line) { parse_error(p, "EOF in func"); return NULL; }

    
    const char *s = line + 4;  
    while (*s && isspace((unsigned char)*s)) s++;

    char *name = NULL;
    if (*s == '"') {
        const char *endp = NULL;
        name = extract_quoted(s, &endp);
        free(line);
        if (!name) {
            parse_error(p, "expected quoted function name after 'func'");
            return NULL;
        }
    } else {
        
        const char *start = s;
        while (*s && !isspace((unsigned char)*s)) s++;
        if (s == start) {
            free(line);
            parse_error(p, "expected function name after 'func'");
            return NULL;
        }
        name = xstrndup(start, (size_t)(s - start));
        free(line);
    }

    Func *f = xmalloc(sizeof(Func));
    memset(f, 0, sizeof(*f));
    f->name = name;

    
    f->body = parse_stmt_list(p, NULL);
    if (p->error) {
        func_free(f);
        return NULL;
    }

    
    const char *cl = peek(p);
    if (!cl || cl[0] != '}') {
        parse_error(p, "expected '}' to close func");
        func_free(f);
        return NULL;
    }
    char *cll = consume(p);
    free(cll);

    return f;
}

static void parse_ztslo_block(Parser *p, Program *prog) {
    char *line = consume(p);  
    free(line);
    prog->inline_ztslo_used = true;

    while (true) {
        const char *l = peek(p);
        if (!l) { parse_error(p, "EOF in ztslo block"); return; }
        if (starts_with_kw(l, "zstlo.end")) {
            zt_warn("typo 'zstlo.end'; did you mean 'ztslo.end'?");
        }
        if (starts_with_kw(l, "ztslo.end") || starts_with_kw(l, "zstlo.end")) {
            char *e = consume(p);
            free(e);
            return;
        }
        if (starts_with_kw(l, "define")) {
            Stmt *s = parse_define(p, NULL);
            if (!s) {
                if (p->error) return;
                continue;
            }
            
            Var *v = xmalloc(sizeof(Var));
            v->name  = xstrdup(s->define.name);
            v->value = xstrdup(s->define.value);
            v->next = prog->vars;
            prog->vars = v;
            stmt_free(s);
            continue;
        }
        
        if (l[0] == '}' && l[1] == '\0') {
            char *skip = consume(p);
            free(skip);
            continue;
        }
        
        char *skip = consume(p);
        if (skip) {
            if (reject_if_misplaced_statement(p, skip)) {
                free(skip);
                return;
            }
            const char *sug = suggest_keyword(skip);
            if (sug) {
                zt_error("unknown line in ztslo: '%s' (did you mean '%s'?)", skip, sug);
                free(skip);
                parse_error(p, "unknown line with suggestion");
                return;
            }
            zt_warn("skipping line in ztslo: %s", skip);
            free(skip);
        }
    }
}

static void parse_ztsl_block(Parser *p, Program *prog) {
    char *line = consume(p);  
    free(line);

    while (true) {
        const char *l = peek(p);
        if (!l) { parse_error(p, "EOF in ztsl block"); return; }
        if (starts_with_kw(l, "zstl.end")) {
            zt_warn("typo 'zstl.end'; did you mean 'ztsl.end'?");
        }
        if (starts_with_kw(l, "ztsl.end") || starts_with_kw(l, "zstl.end")) {
            char *e = consume(p);
            free(e);
            return;
        }
        if (starts_with_kw(l, "ztslo.start")) {
            parse_ztslo_block(p, prog);
            if (p->error) return;
            continue;
        }
        if (starts_with_kw(l, "zstlo.start")) {
            zt_warn("typo 'zstlo.start'; did you mean 'ztslo.start'?");
            parse_ztslo_block(p, prog);
            if (p->error) return;
            continue;
        }
        if (starts_with_kw(l, "zstlo.end")) {
            zt_warn("typo 'zstlo.end'; did you mean 'ztslo.end'?");
        }
        if (starts_with_kw(l, "ztslo.end") || starts_with_kw(l, "zstlo.end")) {
            
            char *e = consume(p);
            free(e);
            continue;
        }
        if (starts_with_kw(l, "func")) {
            Func *f = parse_func(p);
            if (!f) {
                if (p->error) return;
                continue;
            }
            f->next = prog->funcs;
            prog->funcs = f;
            continue;
        }
        
        if (l[0] == '}' && l[1] == '\0') {
            char *skip = consume(p);
            free(skip);
            continue;
        }
        
        char *skip = consume(p);
        if (skip) {
            if (reject_if_misplaced_statement(p, skip)) {
                free(skip);
                return;
            }
            const char *sug = suggest_keyword(skip);
            if (sug) {
                zt_error("unknown top-level line: '%s' (did you mean '%s'?)", skip, sug);
                free(skip);
                parse_error(p, "unknown line with suggestion");
                return;
            }
            zt_warn("skipping top-level line: %s", skip);
            free(skip);
        }
    }
}

static void parse_program(Parser *p, Program *prog) {
    while (true) {
        const char *l = peek(p);
        if (!l) break;
        if (starts_with_kw(l, "zstl.start")) {
            zt_warn("typo 'zstl.start'; did you mean 'ztsl.start'?");
        } else if (starts_with_kw(l, "zstl.end")) {
            zt_warn("typo 'zstl.end'; did you mean 'ztsl.end'?");
        }
        if (starts_with_kw(l, "ztsl.start") || starts_with_kw(l, "zstl.start")) {
            parse_ztsl_block(p, prog);
            if (p->error) return;
            continue;
        }
        if (starts_with_kw(l, "ztslo.start")) {
            parse_ztslo_block(p, prog);
            if (p->error) return;
            continue;
        }
        if (l[0] == '}' && l[1] == '\0') {
            char *skip = consume(p);
            free(skip);
            continue;
        }
        char *skip = consume(p);
        if (skip) {
            if (reject_if_misplaced_statement(p, skip)) {
                free(skip);
                return;
            }
            const char *sug = suggest_keyword(skip);
            if (sug) {
                zt_error("unknown top-level line: '%s' (did you mean '%s'?)", skip, sug);
                free(skip);
                parse_error(p, "unknown line with suggestion");
                return;
            }
            zt_warn("skipping top-level line: %s", skip);
            free(skip);
        }
    }
}

static Var *var_find(Var *head, const char *name) {
    for (Var *v = head; v; v = v->next)
        if (strcasecmp(v->name, name) == 0) return v;
    return NULL;
}

static void var_set(Var **head, const char *name, const char *value) {
    Var *v = var_find(*head, name);
    if (v) {
        free(v->value);
        v->value = xstrdup(value);
        return;
    }
    v = xmalloc(sizeof(Var));
    v->name  = xstrdup(name);
    v->value = xstrdup(value);
    v->next = *head;
    *head = v;
}

static char *subst_vars(const char *s, Var *vars) {
    dstring out;
    dstr_init(&out);
    const char *p = s;
    while (*p) {
        if (*p == '@') {
            
            const char *start = p + 1;
            const char *q = start;
            if (isalpha((unsigned char)*q) || *q == '_') {
                while (isalnum((unsigned char)*q) || *q == '_') q++;
                size_t namelen = (size_t)(q - start);
                char *name = xstrndup(start, namelen);
                Var *v = var_find(vars, name);
                if (v) {
                    dstr_append_cstr(&out, v->value);
                } else {
                    
                    dstr_append_char(&out, '@');
                    dstr_append_cstr(&out, name);
                }
                free(name);
                p = q;
                continue;
            }
        }
        dstr_append_char(&out, *p);
        p++;
    }
    return out.data;
}

typedef struct {
    Program *prog;
    Var    **vars;       
    bool     verbose;
    bool     dry_run;    
    bool     force;      
    dstring  gen_c;      
} ExecCtx;

static bool path_is_empty_file(const char *path) {
    struct stat st;
    if (stat(path, &st) != 0) {
        
        return true;
    }
    if (!S_ISREG(st.st_mode)) {
        
        return false;
    }
    return st.st_size == 0;
}

static double quantize_mantissa_bits(double v, int keep_bits) {
    
    if (v == 0.0 || !isfinite(v) || keep_bits >= 52) return v;
    uint64_t bits;
    memcpy(&bits, &v, sizeof(bits));
    int drop = 52 - keep_bits;
    uint64_t half = (uint64_t)1 << (drop - 1);
    uint64_t mask = ((uint64_t)1 << drop) - 1;
    uint64_t frac = bits & mask;
    bits &= ~mask;
    if (frac >= half) bits += ((uint64_t)1 << drop);
    memcpy(&v, &bits, sizeof(bits));
    return v;
}

static char *compute_float_calc(int width, const char *lhs_s, char op,
                                const char *rhs_s) {
    char buf[80];

    if (width == 32) {
        float a = strtof(lhs_s, NULL);
        float b = strtof(rhs_s, NULL);
        float r = 0;
        switch (op) {
            case '+': r = a + b; break;
            case '-': r = a - b; break;
            case '*': r = a * b; break;
            case '/':
                if (b == 0.0f) { return NULL; }
                r = a / b;
                break;
        }
        snprintf(buf, sizeof(buf), "%.9g", (double)r);
    } else if (width == 64 || width == 42) {
        double a = strtod(lhs_s, NULL);
        double b = strtod(rhs_s, NULL);
        double r = 0;
        switch (op) {
            case '+': r = a + b; break;
            case '-': r = a - b; break;
            case '*': r = a * b; break;
            case '/':
                if (b == 0.0) { return NULL; }
                r = a / b;
                break;
        }
        if (width == 42) r = quantize_mantissa_bits(r, 30);
        snprintf(buf, sizeof(buf), "%.17g", r);
    } else if (width == 76) {
        
        long double a = strtold(lhs_s, NULL);
        long double b = strtold(rhs_s, NULL);
        long double r = 0;
        switch (op) {
            case '+': r = a + b; break;
            case '-': r = a - b; break;
            case '*': r = a * b; break;
            case '/':
                if (b == 0.0L) { return NULL; }
                r = a / b;
                break;
        }
        snprintf(buf, sizeof(buf), "%.21Lg", r);
    } else { 
        
        __float128 a = strtold(lhs_s, NULL);
        __float128 b = strtold(rhs_s, NULL);
        __float128 r = 0;
        switch (op) {
            case '+': r = a + b; break;
            case '-': r = a - b; break;
            case '*': r = a * b; break;
            case '/':
                if (b == 0.0L) { return NULL; }
                r = a / b;
                break;
        }
        
        long double disp = (long double)r;
        snprintf(buf, sizeof(buf), "%.21Lg", disp);
    }
    return xstrdup(buf);
}

static bool eval_cond(Cond *c, Var *vars) {
    if (c->kind == COND_EMPTYFILE) {
        Var *v = var_find(vars, c->var);
        const char *path = v ? v->value : "";
        bool empty = path_is_empty_file(path);
        return c->is_is ? empty : !empty;
    }

    char *file_content = NULL;
    const char *val;
    if (c->subj == SUBJ_READFILE) {
        char *path = subst_vars(c->path, vars);
        file_content = read_file(path);
        free(path);
        if (!file_content) file_content = xstrdup("");
        val = file_content;
    } else {
        Var *v = var_find(vars, c->var);
        val = v ? v->value : "";
    }

    bool result = false;
    if (c->is_is) {
        
        for (size_t i = 0; i < c->nvalues; i++) {
            char *sv = subst_vars(c->values[i], vars);
            bool eq = (strcmp(sv, val) == 0);
            free(sv);
            if (eq) { result = true; break; }
        }
    } else {
        
        result = true;
        for (size_t i = 0; i < c->nvalues; i++) {
            char *sv = subst_vars(c->values[i], vars);
            bool eq = (strcmp(sv, val) == 0);
            free(sv);
            if (eq) { result = false; break; }
        }
    }
    free(file_content);
    return result;
}

static char **split_args(const char *cmd, int *argc_out) {
    
    int argc = 0;
    const char *p = cmd;
    bool in_quote = false;
    while (*p) {
        while (*p && isspace((unsigned char)*p) && !in_quote) p++;
        if (!*p) break;
        argc++;
        while (*p && (!isspace((unsigned char)*p) || in_quote)) {
            if (*p == '"') in_quote = !in_quote;
            p++;
        }
    }
    if (argc == 0) {
        *argc_out = 0;
        return NULL;
    }
    char **argv = xmalloc(sizeof(char *) * (size_t)(argc + 1));
    int i = 0;
    p = cmd;
    in_quote = false;
    while (*p) {
        while (*p && isspace((unsigned char)*p) && !in_quote) p++;
        if (!*p) break;
        const char *start = p;
        dstring tok;
        dstr_init(&tok);
        while (*p && (!isspace((unsigned char)*p) || in_quote)) {
            if (*p == '"') {
                in_quote = !in_quote;
                p++;
                continue;
            }
            dstr_append_char(&tok, *p);
            p++;
        }
        (void)start;
        argv[i++] = tok.data;
    }
    argv[argc] = NULL;
    *argc_out = argc;
    return argv;
}

static void free_args(char **argv) {
    if (!argv) return;
    for (int i = 0; argv[i]; i++) free(argv[i]);
    free(argv);
}

static int run_shell(const char *cmd) {
    int rc = system(cmd);
    if (rc == -1) {
        zt_error("system() failed: %s", strerror(errno));
        return -1;
    }
    if (WIFEXITED(rc)) return WEXITSTATUS(rc);
    if (WIFSIGNALED(rc)) {
        zt_error("command terminated by signal %d", WTERMSIG(rc));
        return 128 + WTERMSIG(rc);
    }
    return rc;
}

static int run_exec(const char *cmd) {
    int argc = 0;
    char **argv = split_args(cmd, &argc);
    if (argc == 0 || !argv) {
        zt_error("empty exec command");
        free_args(argv);
        return -1;
    }

    
    char *prog_name = xstrdup(argv[0]);

    pid_t pid = fork();
    if (pid < 0) {
        zt_error("fork() failed: %s", strerror(errno));
        free(prog_name);
        free_args(argv);
        return -1;
    }
    if (pid == 0) {
        
        execvp(argv[0], argv);
        
        fprintf(stderr, "E: execvp(%s) failed: %s\n",
                argv[0], strerror(errno));
        _exit(127);
    }
    
    int status = 0;
    pid_t w;
    do {
        w = waitpid(pid, &status, 0);
    } while (w < 0 && errno == EINTR);

    free_args(argv);
    if (w < 0) {
        zt_error("waitpid() failed: %s", strerror(errno));
        free(prog_name);
        return -1;
    }
    if (WIFEXITED(status)) {
        free(prog_name);
        return WEXITSTATUS(status);
    }
    if (WIFSIGNALED(status)) {
        zt_error("%s terminated by signal %d",
                prog_name, WTERMSIG(status));
        free(prog_name);
        return 128 + WTERMSIG(status);
    }
    free(prog_name);
    return 0;
}

static void c_escape_append(dstring *out, const char *s) {
    dstr_append_char(out, '"');
    for (; *s; s++) {
        switch (*s) {
            case '"':  dstr_append_cstr(out, "\\\""); break;
            case '\\': dstr_append_cstr(out, "\\\\"); break;
            case '\n': dstr_append_cstr(out, "\\n");  break;
            case '\r': dstr_append_cstr(out, "\\r");  break;
            case '\t': dstr_append_cstr(out, "\\t");  break;
            default:
                if ((unsigned char)*s < 0x20) {
                    char buf[8];
                    snprintf(buf, sizeof(buf), "\\x%02x",
                             (unsigned char)*s);
                    dstr_append_cstr(out, buf);
                } else {
                    dstr_append_char(out, *s);
                }
                break;
        }
    }
    dstr_append_char(out, '"');
}

static int exec_stmt(ExecCtx *ctx, Stmt *s);

static int exec_stmt_list(ExecCtx *ctx, Stmt *list) {
    for (Stmt *s = list; s; s = s->next) {
        int rc = exec_stmt(ctx, s);
        if (rc != 0) return rc;
    }
    return 0;
}

static int exec_stmt(ExecCtx *ctx, Stmt *s) {
    switch (s->kind) {
        case K_DEFINE: {
            char *val = subst_vars(s->define.value, *ctx->vars);
            var_set(ctx->vars, s->define.name, val);
            if (ctx->verbose)
                fprintf(stderr, "[define] %s = %s\n", s->define.name, val);
            free(val);
            return 0;
        }
        case K_IF: {
            bool ok = eval_cond(&s->cond, *ctx->vars);
            if (ctx->verbose) {
                const char *subj_desc = (s->cond.subj == SUBJ_READFILE)
                    ? s->cond.path : s->cond.var;
                const char *subj_label = (s->cond.subj == SUBJ_READFILE)
                    ? "read_file " : "";
                if (s->cond.kind == COND_EMPTYFILE) {
                    fprintf(stderr, "[if] %s%s %s an empty file -> %s\n",
                            subj_label, subj_desc, s->cond.is_is ? "is" : "is not",
                            ok ? "true" : "false");
                } else {
                    fprintf(stderr, "[if] %s%s %s -> %s\n",
                            subj_label, subj_desc, s->cond.is_is ? "is" : "is not",
                            ok ? "true" : "false");
                }
            }
            return exec_stmt_list(ctx, ok ? s->cond.then_branch
                                          : s->cond.else_branch);
        }
        case K_EXEC: {
            char *code = subst_vars(s->exec.code, *ctx->vars);
            if (ctx->dry_run) {
                
                if (s->exec.is_shell) {
                    dstr_append_cstr(&ctx->gen_c, "    if (system(");
                    c_escape_append(&ctx->gen_c, code);
                    dstr_append_cstr(&ctx->gen_c, ") != 0) return 1;\n");
                } else {
                    dstr_append_cstr(&ctx->gen_c, "    if (do_exec(");
                    c_escape_append(&ctx->gen_c, code);
                    dstr_append_cstr(&ctx->gen_c, ") != 0) return 1;\n");
                }
                free(code);
                return 0;
            }
            if (ctx->verbose) {
                fprintf(stderr, "[%s] %s\n",
                        s->exec.is_shell ? "shell" : "exec", code);
            }
            int rc;
            if (s->exec.is_shell) rc = run_shell(code);
            else                  rc = run_exec(code);
            free(code);
            return rc;
        }
        case K_SHOW: {
            char *code = subst_vars(s->show.code, *ctx->vars);
            if (ctx->dry_run) {
                dstr_append_cstr(&ctx->gen_c, "    fputs(");
                c_escape_append(&ctx->gen_c, code);
                dstr_append_cstr(&ctx->gen_c, ", stdout);\n");
            } else {
                fputs(code, stdout);
                fflush(stdout);
            }
            free(code);
            return 0;
        }
        case K_DELETE: {
            char *path = subst_vars(s->delfile.path, *ctx->vars);
            if (ctx->dry_run) {
                dstr_append_cstr(&ctx->gen_c, "    if (remove(");
                c_escape_append(&ctx->gen_c, path);
                dstr_append_cstr(&ctx->gen_c,
                    ") != 0 && errno != ENOENT) return 1;\n");
                free(path);
                return 0;
            }
            if (ctx->verbose) fprintf(stderr, "[delete_file] %s\n", path);
            errno = 0;
            int rc = 0;
            if (remove(path) != 0 && errno != ENOENT) {
                zt_error("delete_file %s: %s", path, strerror(errno));
                rc = 1;
            }
            free(path);
            return rc;
        }
        case K_CREATE: {
            char *path = subst_vars(s->mkfile.path, *ctx->vars);
            if (ctx->dry_run) {
                dstr_append_cstr(&ctx->gen_c, "    { FILE *ztc_f = fopen(");
                c_escape_append(&ctx->gen_c, path);
                dstr_append_cstr(&ctx->gen_c,
                    ", \"a\"); if (!ztc_f) return 1; fclose(ztc_f); }\n");
                free(path);
                return 0;
            }
            if (ctx->verbose) fprintf(stderr, "[create_file] %s\n", path);
            FILE *f = fopen(path, "a");
            if (!f) {
                zt_error("create_file %s: %s", path, strerror(errno));
                free(path);
                return 1;
            }
            fclose(f);
            free(path);
            return 0;
        }
        case K_WRITE:
        case K_APPEND: {
            char *path = subst_vars(s->writefile.path, *ctx->vars);
            char *content = subst_vars(s->writefile.code, *ctx->vars);
            const char *mode = (s->kind == K_WRITE) ? "w" : "a";
            if (ctx->dry_run) {
                dstr_append_cstr(&ctx->gen_c, "    { FILE *ztc_f = fopen(");
                c_escape_append(&ctx->gen_c, path);
                dstr_append_cstr(&ctx->gen_c, ", ");
                c_escape_append(&ctx->gen_c, mode);
                dstr_append_cstr(&ctx->gen_c,
                    "); if (!ztc_f) return 1; fputs(");
                c_escape_append(&ctx->gen_c, content);
                dstr_append_cstr(&ctx->gen_c, ", ztc_f); fclose(ztc_f); }\n");
                free(path);
                free(content);
                return 0;
            }
            if (ctx->verbose)
                fprintf(stderr, "[%s] %s\n",
                        s->kind == K_WRITE ? "write_on_file" : "append_file",
                        path);
            FILE *f = fopen(path, mode);
            if (!f) {
                zt_error("%s %s: %s",
                        s->kind == K_WRITE ? "write_on_file" : "append_file",
                        path, strerror(errno));
                free(path);
                free(content);
                return 1;
            }
            fputs(content, f);
            fclose(f);
            free(path);
            free(content);
            return 0;
        }
        case K_CCOMPAT: {
            if (ctx->dry_run) {
                char *code = subst_vars(s->ccompat.code, *ctx->vars);
                dstr_append_cstr(&ctx->gen_c, "    {\n");
                dstr_append_cstr(&ctx->gen_c, code);
                dstr_append_cstr(&ctx->gen_c, "\n    }\n");
                free(code);
                return 0;
            }
            zt_warn("ccompat requires -e/-o (C transpile) mode; "
                    "skipping raw C block in interpreted run");
            return 0;
        }
        case K_FLOATCALC: {
            char *lhs_s = subst_vars(s->floatcalc.lhs_raw, *ctx->vars);
            char *rhs_s = subst_vars(s->floatcalc.rhs_raw, *ctx->vars);
            char *result = compute_float_calc(s->floatcalc.width, lhs_s,
                    s->floatcalc.op, rhs_s);
            free(lhs_s);
            free(rhs_s);
            if (!result) {
                zt_error("float%d_calculate: division by zero",
                        s->floatcalc.width);
                return 1;
            }
            var_set(ctx->vars, s->floatcalc.varname, result);
            if (ctx->verbose)
                fprintf(stderr, "[float%d_calculate] %s = %s\n",
                        s->floatcalc.width, s->floatcalc.varname, result);
            free(result);
            return 0;
        }
    }
    return 0;
}

static char *sha256_hex(const char *data, size_t len);

static void serialize_stmt(dstring *out, Stmt *s);

static void serialize_stmt_list(dstring *out, Stmt *s) {
    for (Stmt *cur = s; cur; cur = cur->next) {
        serialize_stmt(out, cur);
    }
}

static void serialize_stmt(dstring *out, Stmt *s) {
    if (!s) return;
    switch (s->kind) {
        case K_DEFINE:
            dstr_append_cstr(out, "DEFINE ");
            dstr_append_cstr(out, s->define.name);
            dstr_append_cstr(out, " AS ");
            dstr_append_cstr(out, s->define.value);
            dstr_append_char(out, '\n');
            break;
        case K_IF:
            dstr_append_cstr(out, "IF ");
            if (s->cond.subj == SUBJ_READFILE) {
                dstr_append_cstr(out, "READFILE ");
                dstr_append_cstr(out, s->cond.path);
            } else {
                dstr_append_cstr(out, s->cond.var);
            }
            if (s->cond.kind == COND_EMPTYFILE) {
                dstr_append_cstr(out, s->cond.is_is ? " ISEMPTYFILE" : " ISNOTEMPTYFILE");
                dstr_append_cstr(out, " THEN\n");
            } else {
                dstr_append_cstr(out, s->cond.is_is ? " IS " : " ISNOT ");
                for (size_t i = 0; i < s->cond.nvalues; i++) {
                    if (i > 0) dstr_append_cstr(out, " OR ");
                    dstr_append_cstr(out, s->cond.values[i]);
                }
                dstr_append_cstr(out, " THEN\n");
            }
            serialize_stmt_list(out, s->cond.then_branch);
            if (s->cond.else_branch) {
                dstr_append_cstr(out, "ELSE\n");
                serialize_stmt_list(out, s->cond.else_branch);
            }
            dstr_append_cstr(out, "ENDIF\n");
            break;
        case K_EXEC:
            dstr_append_cstr(out, "EXEC ");
            dstr_append_cstr(out, s->exec.is_shell ? "SHELL\n" : "EXECP\n");
            dstr_append_cstr(out, s->exec.code);
            dstr_append_char(out, '\n');
            break;
        case K_SHOW:
            dstr_append_cstr(out, "SHOW\n");
            dstr_append_cstr(out, s->show.code);
            dstr_append_char(out, '\n');
            break;
        case K_DELETE:
            dstr_append_cstr(out, "DELETE ");
            dstr_append_cstr(out, s->delfile.path);
            dstr_append_char(out, '\n');
            break;
        case K_CREATE:
            dstr_append_cstr(out, "CREATE ");
            dstr_append_cstr(out, s->mkfile.path);
            dstr_append_char(out, '\n');
            break;
        case K_WRITE:
        case K_APPEND:
            dstr_append_cstr(out, s->kind == K_WRITE ? "WRITE " : "APPEND ");
            dstr_append_cstr(out, s->writefile.path);
            dstr_append_char(out, '\n');
            dstr_append_cstr(out, s->writefile.code);
            dstr_append_char(out, '\n');
            break;
        case K_CCOMPAT:
            dstr_append_cstr(out, "CCOMPAT\n");
            dstr_append_cstr(out, s->ccompat.code);
            dstr_append_char(out, '\n');
            break;
        case K_FLOATCALC: {
            char widthbuf[16];
            snprintf(widthbuf, sizeof(widthbuf), "%d", s->floatcalc.width);
            dstr_append_cstr(out, "FLOATCALC float");
            dstr_append_cstr(out, widthbuf);
            dstr_append_char(out, ' ');
            dstr_append_cstr(out, s->floatcalc.lhs_raw);
            dstr_append_char(out, ' ');
            dstr_append_char(out, s->floatcalc.op);
            dstr_append_char(out, ' ');
            dstr_append_cstr(out, s->floatcalc.rhs_raw);
            dstr_append_cstr(out, " AS ");
            dstr_append_cstr(out, s->floatcalc.varname);
            dstr_append_char(out, '\n');
            break;
        }
    }
}

static char *compute_func_hash(const char *global_hash, Func *fn) {
    dstring buf;
    dstr_init(&buf);
    dstr_append_cstr(&buf, "GH=");
    dstr_append_cstr(&buf, global_hash);
    dstr_append_cstr(&buf, "\nFN=");
    dstr_append_cstr(&buf, fn->name);
    dstr_append_cstr(&buf, "\nBODY:\n");
    serialize_stmt_list(&buf, fn->body);
    char *h = sha256_hex(buf.data, buf.len);
    dstr_free(&buf);
    return h;
}

static char *sha256_hex(const char *data, size_t len) {
    unsigned char digest[SHA256_DIGEST_LENGTH];
    SHA256((const unsigned char *)data, len, digest);
    char *out = xmalloc(SHA256_DIGEST_LENGTH * 2 + 1);
    for (int i = 0; i < SHA256_DIGEST_LENGTH; i++)
        snprintf(out + i * 2, 3, "%02x", digest[i]);
    return out;
}

static char *strip_comments(const char *src) {
    dstring out;
    dstr_init(&out);
    const char *p = src;
    bool in_fence = false;
    bool line_has_code = false;
    while (*p) {
        if (*p == '`' && p[1] == '`' && p[2] == '`') {
            in_fence = !in_fence;
            dstr_append_cstr(&out, "```");
            p += 3;
            continue;
        }
        if (!in_fence && *p == '#') {
            
            bool whole_line_comment = !line_has_code;
            
            while (*p && *p != '\n') p++;
            if (whole_line_comment) {
                
                if (*p == '\n') p++;
            } else {
                
                while (out.len > 0 && (out.data[out.len-1] == ' ' ||
                                       out.data[out.len-1] == '\t')) {
                    out.len--;
                }
                out.data[out.len] = '\0';
                if (*p == '\n') {
                    dstr_append_char(&out, '\n');
                    p++;
                }
            }
            line_has_code = false;
            continue;
        }
        if (*p == '\n') {
            line_has_code = false;
        } else if (!isspace((unsigned char)*p)) {
            line_has_code = true;
        }
        dstr_append_char(&out, *p);
        p++;
    }
    return out.data;
}

static char *read_stored_hash(const char *hashdir, const char *name) {
    char path[1024];
    snprintf(path, sizeof(path), "%s/%s.sha256", hashdir, name);
    FILE *f = fopen(path, "r");
    if (!f) return NULL;
    char buf[128];
    size_t n = fread(buf, 1, sizeof(buf) - 1, f);
    fclose(f);
    buf[n] = '\0';

    if (n == 0) return xstrdup("");

    char *end = buf + n - 1;
    while (end >= buf && isspace((unsigned char)*end)) *end-- = '\0';
    return xstrdup(buf);
}

static void write_stored_hash(const char *hashdir, const char *name,
                              const char *hash) {
    char path[1024];
    snprintf(path, sizeof(path), "%s/%s.sha256", hashdir, name);
    FILE *f = fopen(path, "w");
    if (!f) {
        zt_error("cannot write hash file %s: %s",
                path, strerror(errno));
        return;
    }
    fprintf(f, "%s\n", hash);
    fclose(f);
}

static int transpile_to_c(ExecCtx *ctx, const char *out_path) {
    

    
    Func *f = ctx->prog->funcs;
    
    Func *rev = NULL;
    while (f) {
        Func *next = f->next;
        f->next = rev;
        rev = f;
        f = next;
    }
    ctx->prog->funcs = rev;

    bool exec_used = false;
    dstring body;
    dstr_init(&body);
    for (Func *fn = ctx->prog->funcs; fn; fn = fn->next) {
        dstr_init(&ctx->gen_c);  

        dstring hdr;
        dstr_init(&hdr);
        dstr_append_cstr(&hdr, "    /* func \"");
        dstr_append_cstr(&hdr, fn->name);
        dstr_append_cstr(&hdr, "\" */\n");
        exec_stmt_list(ctx, fn->body);

        
        if (strstr(ctx->gen_c.data, "do_exec(") != NULL) {
            exec_used = true;
        }

        dstr_append_cstr(&body, hdr.data);
        dstr_append_cstr(&body, ctx->gen_c.data);
        dstr_free(&hdr);
        dstr_free(&ctx->gen_c);
    }

    
    dstring src;
    dstr_init(&src);
    dstr_append_cstr(&src,
        "/* Auto-generated by ztc -e. Do not edit. */\n"
        "#define _POSIX_C_SOURCE 200809L\n"
        "#include <stdio.h>\n"
        "#include <stdlib.h>\n"
        "#include <string.h>\n"
        "#include <stdbool.h>\n"
        "#include <unistd.h>\n"
        "#include <sys/wait.h>\n"
        "#include <sys/types.h>\n"
        "#include <errno.h>\n\n");
    if (exec_used) {
        dstr_append_cstr(&src,
            "/* split_args: respects double-quoted arguments (matches ztc runtime) */\n"
            "static int do_split_args(const char *cmd, char **argv, int max) {\n"
            "    int argc = 0;\n"
            "    const char *p = cmd;\n"
            "    while (*p && argc < max - 1) {\n"
            "        while (*p && (*p == ' ' || *p == '\\t' || *p == '\\n')) p++;\n"
            "        if (!*p) break;\n"
            "        char *tok = NULL;\n"
            "        size_t cap = 16, len = 0;\n"
            "        tok = malloc(cap);\n"
            "        if (!tok) return -1;\n"
            "        bool in_quote = false;\n"
            "        while (*p && (!(*p == ' ' || *p == '\\t' || *p == '\\n') || in_quote)) {\n"
            "            if (*p == '\"') { in_quote = !in_quote; p++; continue; }\n"
            "            if (len + 1 >= cap) { cap *= 2; tok = realloc(tok, cap); if (!tok) return -1; }\n"
            "            tok[len++] = *p++;\n"
            "        }\n"
            "        tok[len] = '\\0';\n"
            "        argv[argc++] = tok;\n"
            "    }\n"
            "    argv[argc] = NULL;\n"
            "    return argc;\n"
            "}\n\n"
            "static void do_free_args(char **argv) {\n"
            "    if (!argv) return;\n"
            "    for (int i = 0; argv[i]; i++) free(argv[i]);\n"
            "}\n\n"
            "static int do_exec(const char *cmd) {\n"
            "    char *argv[256];\n"
            "    int argc = do_split_args(cmd, argv, 256);\n"
            "    if (argc <= 0) return 0;\n"
            "    pid_t pid = fork();\n"
            "    if (pid < 0) { do_free_args(argv); return -1; }\n"
            "    if (pid == 0) {\n"
            "        execvp(argv[0], argv);\n"
            "        fprintf(stderr, \"execvp(%s) failed: %s\\n\",\n"
            "                argv[0], strerror(errno));\n"
            "        _exit(127);\n"
            "    }\n"
            "    int status = 0;\n"
            "    waitpid(pid, &status, 0);\n"
            "    do_free_args(argv);\n"
            "    if (WIFEXITED(status)) return WEXITSTATUS(status);\n"
            "    return 1;\n"
            "}\n\n");
    }
    dstr_append_cstr(&src, "int main(void) {\n");
    dstr_append_cstr(&src, body.data);
    dstr_append_cstr(&src, "    return 0;\n}\n");

    
    char cpath[1024];
    snprintf(cpath, sizeof(cpath), "%s.c", out_path);
    FILE *cf = fopen(cpath, "w");
    if (!cf) {
        zt_error("cannot open %s: %s",
                cpath, strerror(errno));
        dstr_free(&src);
        dstr_free(&body);
        return -1;
    }
    fwrite(src.data, 1, src.len, cf);
    fclose(cf);

    dstr_free(&src);
    dstr_free(&body);

    
    char *gcc_argv[] = {
        "gcc", "-std=c11", "-Wall", "-Wextra", "-Werror", "-O2",
        cpath, "-o", (char *)out_path, NULL
    };
    if (ctx->verbose) {
        fprintf(stderr, "ztc: invoking: gcc");
        for (char **a = gcc_argv + 1; *a; a++) fprintf(stderr, " %s", *a);
        fprintf(stderr, "\n");
    }
    pid_t pid = fork();
    if (pid < 0) {
        zt_error("fork() failed: %s", strerror(errno));
        return -1;
    }
    if (pid == 0) {
        execvp("gcc", gcc_argv);
        fprintf(stderr, "E: execvp(gcc) failed: %s\n", strerror(errno));
        _exit(127);
    }
    int status = 0;
    waitpid(pid, &status, 0);
    int rc = WIFEXITED(status) ? WEXITSTATUS(status) : 1;
    if (rc != 0) {
        zt_error("gcc failed (rc=%d)", rc);
        return rc;
    }
    fprintf(stderr, "Generated C code and ELF in %s and %s\n", out_path, cpath);
    return 0;
}

static void usage(const char *argv0) {
    fprintf(stderr,
        "ztc %s - ZTSL build tool\n"
        "Usage: %s [options] [target ...]\n"
        "       %s -o <out> <file.ztsl>\n"
        "  -f <file>   Build file (default: build.ztsl)\n"
        "  -e <out>    Transpile to C and produce executable <out>\n"
        "  -o <out>    Same as -e, but takes the .ztsl path as a\n"
        "              positional argument instead of -f\n"
        "  -l          List available functions and exit\n"
        "  -F          Force (ignore cache)\n"
        "  -v          Verbose\n"
        "  -V          Print version and exit\n"
        "  -h          Help\n",
        ZTC_VERSION, argv0, argv0);
}

int main(int argc, char **argv) {
    const char *prog_name = argv[0] ? argv[0] : "ztc";
    const char *pn_slash = strrchr(prog_name, '/');
    if (pn_slash) prog_name = pn_slash + 1;
    const char *build_file = "build.ztsl";
    const char *exec_out   = NULL;
    bool list_only = false;
    bool force = false;
    bool verbose = false;
    bool positional_file = false;

    int opt;
    while ((opt = getopt(argc, argv, "+f:e:o:lFvVh")) != -1) {
        switch (opt) {
            case 'f': build_file = optarg; break;
            case 'e': exec_out   = optarg; break;
            case 'o': exec_out   = optarg; positional_file = true; break;
            case 'l': list_only  = true;   break;
            case 'F': force      = true;   break;
            case 'v': verbose   = true;    break;
            case 'V': printf("ztc %s\n", ZTC_VERSION); return 0;
            case 'h': usage(argv[0]); return 0;
            default:  usage(argv[0]); return 2;
        }
    }

    
    char **targets = NULL;
    int ntargets = 0;
    if (optind < argc) {
        targets = &argv[optind];
        ntargets = argc - optind;
    }

    if (positional_file) {
        if (ntargets < 1) {
            zt_error("-o requires a .ztsl file: ztc -o <out> <file.ztsl>");
            return 2;
        }
        build_file = targets[0];
        if (ntargets > 1) {
            zt_warn("-o converts the whole file; ignoring extra "
                    "arguments after %s", build_file);
        }
        targets = NULL;
        ntargets = 0;
    }

    
    char *content = read_file(build_file);
    if (!content) {
        zt_error("cannot read %s: %s",
                build_file, strerror(errno));
        return 1;
    }

    
    char *stripped_ztsl = strip_comments(content);

    char extfile[1024];
    snprintf(extfile, sizeof(extfile), "%s", build_file);
    char *dot_ext = strrchr(extfile, '.');
    if (dot_ext) strcpy(dot_ext, ".ztslo");
    else         strcat(extfile, ".ztslo");
    char *ext_content = read_file(extfile);

    dstring combined;
    dstr_init(&combined);
    dstr_append_cstr(&combined, stripped_ztsl);
    dstr_append_cstr(&combined, "\n||ZTSLO||\n");
    if (ext_content) {
        char *stripped_ztslo = strip_comments(ext_content);
        dstr_append_cstr(&combined, stripped_ztslo);
        free(stripped_ztslo);
        free(ext_content);
    }
    char *new_hash = sha256_hex(combined.data, combined.len);
    dstr_free(&combined);
    free(stripped_ztsl);

    
    const char *slash = strrchr(build_file, '/');
    const char *base = slash ? slash + 1 : build_file;
    
    char base_noext[256];
    snprintf(base_noext, sizeof(base_noext), "%s", base);
    char *dot = strrchr(base_noext, '.');
    if (dot) *dot = '\0';

    const char *hashdir = "hash";
    mkdir(hashdir, 0755);
    char *stored = read_stored_hash(hashdir, base_noext);

    bool cache_hit = false;
    if (!force && stored && strcmp(stored, new_hash) == 0) {
        cache_hit = true;
    }

    if (verbose) {
        fprintf(stderr, "ztc: build file    = %s\n", build_file);
        fprintf(stderr, "ztc: ztslo file    = %s%s\n", extfile,
                ext_content ? "" : " (not found)");
        fprintf(stderr, "ztc: current hash  = %s\n", new_hash);
        fprintf(stderr, "ztc: stored hash   = %s\n",
                stored ? stored : "(none)");
        fprintf(stderr, "ztc: cache %s\n",
                cache_hit ? "HIT (skipping)" : "MISS (running)");
    }

    
    LineBuf lb;
    linebuf_init(&lb);
    file_to_lines(content, &lb);
    free(content);

    Parser p = { .lb = &lb, .pos = 0, .error = false, .err_msg = NULL };
    Program prog = { .funcs = NULL, .vars = NULL };
    parse_program(&p, &prog);

    if (p.error) {
                zt_error("parse error: %s",
                        p.err_msg ? p.err_msg : "(unknown)");
        free(p.err_msg);
        linebuf_free(&lb);
        var_free(prog.vars);
        func_free(prog.funcs);
        free(new_hash);
        free(stored);
        return 1;
    }

    
    {
        char extfile[1024];
        snprintf(extfile, sizeof(extfile), "%s", build_file);
        char *dot2 = strrchr(extfile, '.');
        if (dot2) strcpy(dot2, ".ztslo");
        else      strcat(extfile, ".ztslo");

        bool ext_exists = (access(extfile, F_OK) == 0);
        if (prog.inline_ztslo_used && ext_exists) {
            zt_warn("inline ztslo block in %s; external %s will be ignored",
                    build_file, extfile);
        }

        if (!prog.inline_ztslo_used && ext_exists) {
            char *ext_content = read_file(extfile);
            if (ext_content) {
                if (verbose) {
                    fprintf(stderr, "ztc: loaded external ztslo: %s\n",
                            extfile);
                }
                LineBuf elb;
                linebuf_init(&elb);
                file_to_lines(ext_content, &elb);
                free(ext_content);

                Parser ep = { .lb = &elb, .pos = 0, .error = false, .err_msg = NULL };
                parse_program(&ep, &prog);
                if (ep.error) {
                    zt_error("parse error in %s: %s",
                            extfile, ep.err_msg ? ep.err_msg : "(unknown)");
                    free(ep.err_msg);
                    linebuf_free(&elb);
                    linebuf_free(&lb);
                    var_free(prog.vars);
                    func_free(prog.funcs);
                    free(new_hash);
                    free(stored);
                    return 1;
                }
                linebuf_free(&elb);
            }
        } else if (!prog.inline_ztslo_used && verbose) {
            fprintf(stderr, "ztc: no inline ztslo and no %s; "
                    "continuing with empty variable table\n", extfile);
        }
    }

    
    if (list_only) {
        
        Func *rev = NULL;
        Func *f = prog.funcs;
        while (f) {
            Func *next = f->next;
            f->next = rev;
            rev = f;
            f = next;
        }
        prog.funcs = rev;
        printf("Available functions in %s:\n", build_file);
        for (Func *fn = prog.funcs; fn; fn = fn->next)
            printf("  - %s\n", fn->name);
        linebuf_free(&lb);
        var_free(prog.vars);
        func_free(prog.funcs);
        free(new_hash);
        free(stored);
        return 0;
    }

    
    if (exec_out) {
        ExecCtx ctx;
        ctx.prog    = &prog;
        ctx.vars    = &prog.vars;
        ctx.verbose = verbose;
        ctx.dry_run = true;
        ctx.force   = force;
        int rc = transpile_to_c(&ctx, exec_out);
        linebuf_free(&lb);
        var_free(prog.vars);
        func_free(prog.funcs);
        free(new_hash);
        free(stored);
        return rc == 0 ? 0 : 1;
    }

    
    if (cache_hit && ntargets == 0) {
        
        bool all_hit = true;
        for (Func *fn = prog.funcs; fn; fn = fn->next) {
            char *fh = compute_func_hash(new_hash, fn);
            char fkey[512];
            snprintf(fkey, sizeof(fkey), "%s.%s", base_noext, fn->name);
            char *stored_fh = read_stored_hash(hashdir, fkey);
            bool hit = (stored_fh && strcmp(stored_fh, fh) == 0);
            if (!hit) { all_hit = false; }
            if (verbose)
                fprintf(stderr, "ztc: func %-20s %s\n", fn->name,
                        hit ? "(cached)" : "(will run)");
            free(fh);
            free(stored_fh);
        }
        if (all_hit) {
            fprintf(stderr,
                    "E: all functions in %s unchanged since last successful run; skipping.\n"
                    "  - to force re-run:    %s -F [%s]\n"
                    "  - to clear all cache: rm -rf hash/\n"
                    "  - to see what's there: %s -l [%s]\n",
                    build_file,
                    prog_name, build_file,
                    prog_name, build_file);
            linebuf_free(&lb);
            var_free(prog.vars);
            func_free(prog.funcs);
            free(new_hash);
            free(stored);
            return 0;
        }
    } else if (cache_hit && verbose) {
        fprintf(stderr, "ztc: global cache hit but specific targets requested; running.\n");
    }

    
    ExecCtx ctx;
    ctx.prog    = &prog;
    ctx.vars    = &prog.vars;
    ctx.verbose = verbose;
    ctx.dry_run = false;
    ctx.force   = force;

    
    Func *rev = NULL;
    Func *f = prog.funcs;
    while (f) {
        Func *next = f->next;
        f->next = rev;
        rev = f;
        f = next;
    }
    prog.funcs = rev;

    int rc = 0;
    if (ntargets == 0) {
        
        for (Func *fn = prog.funcs; fn; fn = fn->next) {
            char *fh = compute_func_hash(new_hash, fn);
            char fkey[512];
            snprintf(fkey, sizeof(fkey), "%s.%s", base_noext, fn->name);
            char *stored_fh = read_stored_hash(hashdir, fkey);
            bool hit = (!force && stored_fh && strcmp(stored_fh, fh) == 0);
            free(stored_fh);

            if (hit) {
                if (verbose)
                    fprintf(stderr, "ztc: === func %s === (cached, skipping)\n",
                            fn->name);
                free(fh);
                continue;
            }

            if (verbose) fprintf(stderr, "ztc: === func %s ===\n",
                                 fn->name);
            rc = exec_stmt_list(&ctx, fn->body);
            if (rc != 0) {
                zt_error("function %s failed (rc=%d)", fn->name, rc);
                free(fh);
                break;
            }
            
            write_stored_hash(hashdir, fkey, fh);
            free(fh);
        }
    } else {
        
        for (int i = 0; i < ntargets; i++) {
            Func *fn = NULL;
            for (Func *g = prog.funcs; g; g = g->next) {
                if (strcmp(g->name, targets[i]) == 0) { fn = g; break; }
            }
            if (!fn) {
                zt_error("no such function: %s", targets[i]);
                rc = 1;
                break;
            }
            char *fh = compute_func_hash(new_hash, fn);
            char fkey[512];
            snprintf(fkey, sizeof(fkey), "%s.%s", base_noext, fn->name);
            char *stored_fh = read_stored_hash(hashdir, fkey);
            bool hit = (!force && stored_fh && strcmp(stored_fh, fh) == 0);
            free(stored_fh);

            if (hit) {
                if (verbose)
                    fprintf(stderr, "ztc: === func %s === (cached, skipping)\n",
                            fn->name);
                free(fh);
                continue;
            }

            if (verbose) fprintf(stderr, "ztc: === func %s ===\n",
                                 fn->name);
            rc = exec_stmt_list(&ctx, fn->body);
            if (rc != 0) {
                zt_error("function %s failed (rc=%d)", fn->name, rc);
                free(fh);
                break;
            }
            
            write_stored_hash(hashdir, fkey, fh);
            free(fh);
        }
    }

    
    if (rc == 0) {
        
        write_stored_hash(hashdir, base_noext, new_hash);
        if (verbose)
            fprintf(stderr, "ztc: updated global hash for %s\n", base_noext);
    }

    linebuf_free(&lb);
    var_free(prog.vars);
    func_free(prog.funcs);
    free(new_hash);
    free(stored);
    return rc == 0 ? 0 : 1;
}
