#Author: Maksymilian Piotrowski
import ply.lex as lex
class MyLexer(object):
    states = (
    )
    tokens = (
    'ASSIGN', 'COMMA',
    'IF','THEN','ELSE','ENDIF', 'WHILE', 'DO', 'ENDWHILE', 'REPEAT', 'UNTIL', 'READ', 'WRITE', 'VAR', 'BEGIN', 'END', 'PROCEDURE', 'PROGRAM', 'IS',
    'ADD', 'SUB', 'MUL', 'DIV','OP','CP', 'SC', 'MOD',
    'EQ', 'NEQ', 'LOW', 'GRE', 'LOWO', 'GREO',
    'NUMBER', 'ID'
    )
    def t_COMMENT(self,t):
        r'\[([^\]]|\n)*\]'
        t.lexer.lineno += (t.value).count('\n')
        pass
    
    t_ASSIGN = r':='
    t_COMMA = r'\,'
    
    t_IF = r'IF'
    t_THEN = r'THEN'
    t_ELSE = r'ELSE'
    t_ENDIF = r'ENDIF'
    t_WHILE = r'WHILE'
    t_DO = r'DO'
    t_ENDWHILE = r'ENDWHILE'
    t_REPEAT = r'REPEAT'
    t_UNTIL = r'UNTIL'
    t_READ = r'READ'
    t_WRITE = r'WRITE'
    t_VAR = r'VAR'
    t_BEGIN = r'BEGIN'
    t_END = r'END'
    t_PROCEDURE = r'PROCEDURE'
    t_PROGRAM = r'PROGRAM'
    t_IS = r'IS'

    t_SC = r'\;'

    t_ADD  = r'\+'
    t_SUB  = r'-'
    t_MUL  = r'\*'
    t_DIV  = r'/'
    t_MOD  = r'\%'

    t_OP  = r'\('
    t_CP  = r'\)'

    t_NEQ = r'!='
    t_LOWO = r'<='
    t_GREO = r'>='
    t_LOW = r'<'
    t_GRE = r'>'
    t_EQ = r'='

    def t_newline(self,t):
     r'\n+'
     t.lexer.lineno += len(t.value)
     pass
    
    t_ignore = ' \t'

    def t_NUMBER(self,t):
     r'\d+'   
     return t
    def t_ID(self,t):
     r'[_a-z]+'  
     return t


    # Error
    def t_error(self,t):
        print("Zignorowano nieobsługiwany znak '%s'" % t.value[0], "w linii ", str(t.lexer.lineno))
        t.lexer.skip(1)

    def __init__(self):
        self.lexer = lex.lex(module=self)