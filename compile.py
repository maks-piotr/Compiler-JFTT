# Compiler
# Author : Maksymilian Piotrowski
import ply.yacc as yacc
import re
import sys

from compilerflex import MyLexer
from precompileyacc import reduce_numbers

def is_power_of_two(n):
    return ((n & (n-1) == 0) and n != 0)


class EnumeratedString():
    def __init__(self):
        self.lines = []
        self.procedure_location = dict()
    def convert_to_string(self):
        s = ""
        for i in self.lines:
            s += i[0] + "\n"
        return s
    def add_line(self,s,num):
        self.lines.append([(s + ' '),num])

    def append_to_all_lines(self,s):
        for i in range(len(self.lines)):
            self.lines[i][0] = self.lines[i][0] + s
    def merge(self, es):
        for key in es.procedure_location:
            self.procedure_location[key] = es.procedure_location[key] + len(self.lines)
        self.lines += es.lines

    def substitute(self,x,y):
        for i in range(len(self.lines)):
            self.lines[i][0] = re.sub(re.escape(x) + r' ',y,self.lines[i][0])
    def substitute_specific(self,x,y):
        for i in range(len(self.lines)):
            if (self.lines[i][0] == x):
                self.lines[i][0] = y
    #delete line i
    def del_ml(self,i):
        for k in range(len(self.lines)):
            if (k < i):
                p = re.compile(r'LINE\+\d+')
                l = p.findall(self.lines[k][0])
                if (len(l) > 0):
                    p = re.compile(r'\d+')
                    n = p.findall(self.lines[k][0])[0]
                    if (k+int(n) > i):
                        self.lines[k][0] = re.sub(r'LINE\+?-?\d+','LINE+' + str(int(n)-1),self.lines[k][0])
            if (k > i):
                p = re.compile(r'LINE\-\d+')
                l = p.findall(self.lines[k][0])
                if (len(l) > 0):
                    p = re.compile(r'\d+')
                    n = p.findall(self.lines[k][0])[0]
                    if (k-int(n) < i):
                        self.lines[k][0] = re.sub(r'LINE\+?-?\d+','LINE-' + str(int(n)-1),self.lines[k][0])
        del self.lines[i]

        
    #substitute one line to multiple lines
    def substitute_ml(self,x,new_lines):
        for i in range(len(self.lines)):
            old = self.lines[i][0]
            self.lines[i][0] = re.sub(x,new_lines[0],self.lines[i][0])
            if (self.lines[i][0] != old):
                for j in range(i+1,i+len(new_lines)):
                    #print(new_lines[j-i])
                    self.lines.insert(j,[new_lines[j-i],self.lines[i][1]])
                for k in range(len(self.lines)):
                    if (k < i):
                        p = re.compile(r'LINE\+\d+')
                        l = p.findall(self.lines[k][0])
                        if (len(l) > 0):
                            p = re.compile(r'\d+')
                            n = p.findall(self.lines[k][0])[0]
                            if (k+int(n) > i):
                                self.lines[k][0] = re.sub(r'LINE\+?-?\d+','LINE+' + str(int(n)+len(new_lines)-1),self.lines[k][0])
                    if (k > i):
                        p = re.compile(r'LINE\-\d+')
                        l = p.findall(self.lines[k][0])
                        if (len(l) > 0):
                            p = re.compile(r'\d+')
                            n = p.findall(self.lines[k][0])[0]
                            if (k-int(n) > i):
                                self.lines[k][0] = re.sub(r'LINE\+?-?\d+','LINE-' + str(int(n)+len(new_lines)-1),self.lines[k][0])
                        
                for key in self.procedure_location:
                    if self.procedure_location[key] > i:
                        self.procedure_location[key] = self.procedure_location[key] + len(new_lines)
    def add_procedure_location(self,name):
        self.procedure_location[name] = 0
    #zmienia JUMP MAIN na prawidziwa komende
    def add_jump_main(self):
        for i in range(len(self.lines)):
            if self.lines[i][0] == 'JUMP MAIN ':
                self.lines[i][0] = 'JUMP ' + str(self.procedure_location['MAIN'])
    def comment_first_line(self, comment):
        self.lines[0][0] = self.lines[0][0] + ' ' + comment
    def get_number(self,line, match):
        match = match.group()
        p = re.compile('-?\d+')
        n = p.findall(match)[0]
        return str(int(n) + line)
    def fix_lines(self):
        for i in range(len(self.lines)):
            self.lines[i][0] = re.sub(r'LINE\+?-?\d+',lambda match: self.get_number(i,match),self.lines[i][0])

    def look_for_undeclared_variables(self):
        p = re.compile('V[_a-z]+')
        for i in range(len(self.lines)):
            l = p.findall(self.lines[i][0])
            if (len(l) > 0):
                p = re.compile('[_a-z]+')
                name = p.findall(self.lines[i][0])[0]
                return self.lines[i][1],name
        return -1,''
    def look_for_undeclared_procedures(self):
        p = re.compile('[_a-z]+\#')
        for i in range(len(self.lines)):
            l = p.findall(self.lines[i][0])
            if (len(l) > 0):
               p = re.compile('[_a-z]+')
               name = p.findall(self.lines[i][0])[0]
               return self.lines[i][1],name
        return -1,''
    def look_for_uninit_variables(self,names):
        stored = dict()
        for name in names:
            for i in range(len(self.lines)):
                p = re.compile('STORE V' + name + '|GET V' + name + '|SET V' + name)
                l = p.findall(self.lines[i][0])
                if (len(l) > 0):
                    stored[name] = True
                else:
                    p = re.compile('V' + name)
                    l = p.findall(self.lines[i][0])
                    if (len(l) > 0 and (not name in stored)):
                        print("Ostrzeżenie - możliwie niezainicjowana zmienna", name, "użyta w linii", self.lines[i][1])
                

class ParserClass(object):

    tokens = MyLexer.tokens
    def remember_number(self,x):
        if not int(x) in self.number_location:
            self.number_location[int(x)] = self.last_used+1
            self.last_used = self.last_used +1
        return self.number_location[int(x)]
    def store_numbers(self):
        l = EnumeratedString()
        for key, value in self.number_location.items():
            l.add_line('SET ' + str(key),0)
            l.add_line('STORE ' + str(value),0)
        return l

    def mul_alogrithm(self):
        l = EnumeratedString()
        self.pointer_list['MULTIPLICATION'] = []
        l.add_procedure_location('MULTIPLICATION')
        l.add_line('STORE 2', 0)
        l.add_line('JZERO LINE+21', 0)
        l.add_line('SUB 3', 0) #swap
        l.add_line('JPOS LINE+7', 0)
        l.add_line('LOAD 2', 0)
        l.add_line('STORE 4', 0)
        l.add_line('LOAD 3', 0)
        l.add_line('STORE 2', 0)
        l.add_line('LOAD 4', 0)
        l.add_line('STORE 3', 0)
        l.add_line('SET 0', 0) #c - 5
        l.add_line('STORE  5', 0) 
        l.add_line('LOAD 3', 0) #begin
        l.add_line('JZERO LINE+19', 0)

        l.add_line('LOAD 3', 0) #check if b odd, sets flag 4
        l.add_line('HALF', 0)
        l.add_line('STORE 4', 0)
        l.add_line('SET 1', 0)
        l.add_line('ADD 3', 0)
        l.add_line('HALF', 0)
        l.add_line('SUB 4', 0)

        l.add_line('JZERO LINE+4', 0)
        l.add_line('LOAD 5', 0) # c = c+a
        l.add_line('ADD 2', 0)
        l.add_line('STORE 5', 0)

        l.add_line('LOAD 2', 0) # a = a << 1
        l.add_line('ADD 2', 0) 
        l.add_line('STORE 2', 0)

        l.add_line('LOAD 3', 0) # b = b >> 1
        l.add_line('HALF', 0) 
        l.add_line('STORE 3', 0)

        l.add_line('JUMP LINE-19', 0)
        l.add_line('LOAD 5', 0)
        l.add_line('JUMPI 6', 0)

        if (self.comments_on):
            l.comment_first_line('[multiplication]')
        return l
    def div_algorithm(self):
        l = EnumeratedString()
        self.pointer_list['DIVISION'] = []
        l.add_procedure_location('DIVISION')
        self.pointer_list['MODULO'] = []
        l.add_procedure_location('MODULO')

        l.add_line('STORE 6', 0)
        l.add_line('SET 0', 0)
        l.add_line('STORE 2', 0) #D
        l.add_line('STORE 3', 0) #Q
        l.add_line('SET 1', 0)
        l.add_line('STORE 4', 0) #ustawianie 2^i
        l.add_line('LOAD 5', 0) #N
        l.add_line('SUB 4', 0)
        l.add_line('JZERO LINE+5', 0)
        l.add_line('LOAD 4', 0)
        l.add_line('ADD 4', 0)
        l.add_line('STORE 4', 0)
        l.add_line('JUMP LINE-6', 0)
        l.add_line('LOAD 4', 0)
        l.add_line('SUB 5', 0)
        l.add_line('JZERO LINE+4', 0)
        l.add_line('LOAD 4', 0)
        l.add_line('HALF', 0)
        l.add_line('STORE 4', 0)
        l.add_line('LOAD 3', 0)
        l.add_line('ADD 3', 0)
        l.add_line('STORE 3', 0)
        l.add_line('LOAD 5', 0) #chcek if N >= 2^i, if yes R+=1
        l.add_line('SUB 4', 0)
        l.add_line('JPOS LINE+5', 0)
        l.add_line('LOAD 4', 0)
        l.add_line('SUB 5', 0)
        l.add_line('JZERO LINE+2', 0)
        l.add_line('JUMP LINE+5', 0)
        l.add_line('STORE 5', 0)
        l.add_line('SET 1', 0)
        l.add_line('ADD 3', 0)
        l.add_line('STORE 3', 0)
        l.add_line('LOAD 3', 0)
        l.add_line('SUB 7', 0)
        l.add_line('JPOS LINE+4', 0)
        l.add_line('LOAD 7', 0)
        l.add_line('SUB 3', 0)
        l.add_line('JPOS LINE+5', 0)
        l.add_line('STORE 3', 0)
        l.add_line('LOAD 2', 0)
        l.add_line('ADD 4', 0)
        l.add_line('STORE 2', 0)
        l.add_line('LOAD 4', 0)
        l.add_line('HALF', 0)
        l.add_line('JZERO LINE+3', 0)
        l.add_line('STORE 4', 0)
        l.add_line('JUMP LINE-28', 0)
        l.add_line('JUMPI 6', 0)
        
        if (self.comments_on):
            l.comment_first_line('[division]')
        return l
    def mod_algorithm(self):
        l = EnumeratedString()
        self.pointer_list['MODULO'] = []
        l.add_procedure_location('MODULO')

        l.add_line('STORE 6', 0)
        l.add_line('SET 0', 0)
        l.add_line('STORE 3', 0) #Q
        l.add_line('SET 1', 0)
        l.add_line('STORE 4', 0) #ustawianie 2^i
        l.add_line('LOAD 5', 0) #N
        l.add_line('SUB 4', 0)
        l.add_line('JZERO LINE+5', 0)
        l.add_line('LOAD 4', 0)
        l.add_line('ADD 4', 0)
        l.add_line('STORE 4', 0)
        l.add_line('JUMP LINE-6', 0)
        l.add_line('LOAD 4', 0)
        l.add_line('SUB 5', 0)
        l.add_line('JZERO LINE+4', 0)
        l.add_line('LOAD 4', 0)
        l.add_line('HALF', 0)
        l.add_line('STORE 4', 0)
        l.add_line('LOAD 3', 0)
        l.add_line('ADD 3', 0)
        l.add_line('STORE 3', 0)
        l.add_line('LOAD 5', 0) #chcek if N >= 2^i, if yes R+=1
        l.add_line('SUB 4', 0)
        l.add_line('JPOS LINE+5', 0)
        l.add_line('LOAD 4', 0)
        l.add_line('SUB 5', 0)
        l.add_line('JZERO LINE+2', 0)
        l.add_line('JUMP LINE+5', 0)
        l.add_line('STORE 5', 0)
        l.add_line('SET 1', 0)
        l.add_line('ADD 3', 0)
        l.add_line('STORE 3', 0)
        l.add_line('LOAD 3', 0)
        l.add_line('SUB 7', 0)
        l.add_line('JPOS LINE+4', 0)
        l.add_line('LOAD 7', 0)
        l.add_line('SUB 3', 0)
        l.add_line('JPOS LINE+2', 0)
        l.add_line('STORE 3', 0)
        l.add_line('LOAD 4', 0)
        l.add_line('HALF', 0)
        l.add_line('JZERO LINE+3', 0)
        l.add_line('STORE 4', 0)
        l.add_line('JUMP LINE-25', 0)
        l.add_line('JUMPI 6', 0)

        if (self.comments_on):
            l.comment_first_line('[modulo]')
        return l

    def delete_useless_assigns(self, vartab, commands: EnumeratedString):
        for name in vartab:
            used = False
            for i in range(len(commands.lines)):
                p = re.compile('LOAD V' + name + '|ADD V' + name + '|SUB V' + name +'|SET V' + name+'|PUT V' + name)
                l = p.findall(commands.lines[i][0])
                if (len(l)>0):
                    used = True
            if (not used):
                while True:
                    deleted = False
                    for i in range(len(commands.lines)):
                        p = re.compile('@store ' + name)
                        l = p.findall((commands.lines[i][0]))
                        if (len(l)>0):
                            commands.del_ml(i)
                            deleted = True
                            break
                    if (not deleted):
                        break
               
                    


        return commands

    def store_local_variables(self,procedure_name, vartab, commands: EnumeratedString,line):
        err_names = dict()
        for name in vartab:
            if ((vartab.count(name) > 1 or (procedure_name,name) in self.pointer_location)and not name in err_names):
                print("Błąd - podwójna deklaracja zmiennej " + str(name) + " w procedurze " + procedure_name + " w linii " + str(line))
                self.error = True
                err_names[name] = True
            location = self.last_used +1
            self.variable_location[(procedure_name,name)] = location
            self.last_used = self.last_used +1
            commands.substitute('V' + name,str(location))
            #orders = ['ADD ','SUB ','LOAD ','STORE ','SET ','PUT ','GET ']
            #for order in orders:
            #    commands.substitute_specific(order + 'V' + name, order + str(location))
        location = self.last_used +1
        return commands
    def store_pointer_variables(self,procedure_name, vartab, commands: EnumeratedString,line):
        err_names = dict()
        for name in vartab:
            if (vartab.count(name) > 1 and not name in err_names):
                print("Błąd - podwójna deklaracja zmiennej " + str(name) + " w procedurze " + procedure_name + " w linii " + str(line))
                self.error = True
                err_names[name] = True
            location = self.last_used +1
            self.pointer_location[(procedure_name,name)] = location
            if procedure_name in self.pointer_list:
                self.pointer_list[procedure_name] = self.pointer_list[procedure_name] + [name]
            else:
                self.pointer_list[procedure_name] = [name]
            self.pointer_list[procedure_name]
            self.last_used = self.last_used +1
            commands.substitute('ADD V' + name,'ADDI ' + str(location))
            commands.substitute('SUB V' + name,'SUBI ' + str(location))
            #LOAD name jest czasem uzywany bez I - w kontekscie callowania innych funkcji
            commands.substitute('LOAD V' + name,'LOADI ' + str(location))
            commands.substitute('STORE V' + name,'STOREI ' + str(location))
            commands.substitute('SET V' + name,'LOAD ' + str(location))
            commands.substitute_ml('PUT V' + name, ['LOADI ' + str(location), 'PUT 0'])
            commands.substitute_ml('GET V' + name, ['GET 0','STOREI ' + str(location)])

        location = self.last_used +1
        self.pointer_location[(procedure_name,'JUMPI')] = location
        self.last_used = self.last_used +1
        location = self.last_used +1
        if procedure_name in self.pointer_list:
            self.pointer_list[procedure_name] = self.pointer_list[procedure_name] + ['JUMPI']
        else:
            self.pointer_list[procedure_name] = ['JUMPI']
        commands.add_line('JUMPI ' + str(self.pointer_location[(procedure_name,'JUMPI')]), line)
        return commands
    def translate_function_calls(self, commands: EnumeratedString):
        for procedure in self.pointer_list:
            for i in range(len(self.pointer_list[procedure])):
                commands.substitute(procedure + "#" + str(i), str(self.pointer_location[(procedure,self.pointer_list[procedure][i])]))
            commands.substitute("JUMP " + procedure,'JUMP ' + str(commands.procedure_location[procedure]))
        return commands
    def __init__(self, mv):
        self.lexer = MyLexer()
        self.parser = yacc.yacc(module=self)
        self.buffer = ""
        self.number_location = dict() # key - numer, value - jego lokalizacja w pamieci
        self.variable_location = dict() #key - (nazwa procedury,nazwa zmiennej), value - jej lokalizacja w pamieci
        self.pointer_location = dict() #key - (nazwa procedury,nazwa pointera), value - jego lokalizacja w pamieci
                                        #(nazwa procedury, JUMPI) = lokalizacja w pamieci miejsca powrotnego skoku
        self.pointer_list = dict() # key - nazwa procedury, value- upodzadkowana lista jego pointerow
        self.last_used = 10 #ostatnio użyta komórka pamięci, 1 - akumulator do PUT pointer
        self.error = False
        self.multiplication = False
        self.division = False
        self.modulo = False
        self.comments_on = False
        self.max_val = mv
    
    def reset_parser(self):
        self.buffer = ""
        self.parser.restart()

    def p_programall(self,p):
        'programall : procedures main'
        if p[1] != None:
            p[0] = p[1]
            if (self.multiplication == True):
                p[0].merge(self.mul_alogrithm())
            if (self.division == True):
                p[0].merge(self.div_algorithm())
            if (self.division == False and self.modulo == True):
                p[0].merge(self.mod_algorithm())
            if (self.comments_on):
                p[2].comment_first_line('[begin program]')
            p[0].merge(p[2])
            #print(p[0].procedure_location['MAIN']," loc\n")
        else:
            l = EnumeratedString()
            if (self.multiplication == True):
                l.merge(self.mul_alogrithm())
            if (self.division == True):
                l.merge(self.div_algorithm())
            if (self.division == False and self.modulo == True):
                l.merge(self.mod_algorithm())
            if (self.comments_on):
                p[2].comment_first_line('[begin program]')
            l.merge(p[2])
            p[0] = l
        storage = self.store_numbers()
        storage.add_line('JUMP MAIN',p.lineno(2))
        storage.merge(p[0])
        #print(storage.procedure_location['MAIN']," loc\n")
        storage.add_jump_main()
        #print('procedury ', storage.procedure_location)
        storage = self.translate_function_calls(storage)
        undecl = storage.look_for_undeclared_procedures()
        if (undecl[0] != -1):
            print("Błąd - niezadeklarowana procedura " + undecl[1] + " użyta w linii", undecl[0])
            self.error = True
        storage.fix_lines()
        storage.add_line('HALT',p.lineno(2))
        p[0] = storage.convert_to_string()


    def p_procedures_var(self,p):
        'procedures : procedures PROCEDURE ID OP declarations CP IS VAR declarations BEGIN commands END'
        if p[1] != None:
            p[11].add_procedure_location(p[3])
            p[11] = self.delete_useless_assigns(p[9],p[11])
            if (self.comments_on):
                p[11].comment_first_line('[begin procedure ' + str(p[3]) + ']')
            p[11] = self.store_pointer_variables(p[3],p[5],p[11],p.lineno(4))
            p[11].look_for_uninit_variables(p[9])
            p[11] = self.store_local_variables(p[3],p[9],p[11],p.lineno(8))
            undecl = p[11].look_for_undeclared_variables()
            if (undecl[0] != -1):
                print("Błąd - niezadeklarowana zmienna " + undecl[1] + " użyta w linii", undecl[0])
                self.error = True
            l = p[1]
            l.merge(p[11])
            p[0] = l
        else:
            p[11].add_procedure_location(p[3])
            p[11] = self.delete_useless_assigns(p[9],p[11])
            if (self.comments_on):
                p[11].comment_first_line('[begin procedure ' + str(p[3]) + ']')
            p[11] = self.store_pointer_variables(p[3],p[5],p[11],p.lineno(4))
            p[11].look_for_uninit_variables(p[9])
            p[11] = self.store_local_variables(p[3],p[9],p[11],p.lineno(8))
            undecl = p[11].look_for_undeclared_variables()
            if (undecl[0] != -1):
                print("Błąd - niezadeklarowana zmienna " + undecl[1] + " użyta w linii", undecl[0])
                self.error = True
            p[0] = p[11]
    def p_procedures_novar(self,p):
        'procedures : procedures PROCEDURE ID OP declarations CP IS BEGIN commands END'
        if p[1] != None:
            p[9].add_procedure_location(p[3])
            if (self.comments_on):
                p[9].comment_first_line('[begin procedure ' + str(p[3]) + ']')
            p[9] = self.store_pointer_variables(p[3],p[5],p[9],p.lineno(4))
            undecl = p[9].look_for_undeclared_variables()
            if (undecl[0] != -1):
                print("Błąd - niezadeklarowana zmienna " + undecl[1] + " użyta w linii", undecl[0])
                self.error = True
            undecl = p[9].look_for_undeclared_procedures()
            l = p[1]
            l.merge(p[9])
            p[0] = l
        else:
            p[9].add_procedure_location(p[3])
            if (self.comments_on):
                p[9].comment_first_line('[begin procedure ' + str(p[3]) + ']')
            self.store_pointer_variables(p[3],p[5],p[9],p.lineno(4))
            undecl = p[9].look_for_undeclared_variables()
            if (undecl[0] != -1):
                print("Błąd - niezadeklarowana zmienna " + undecl[1] + " użyta w linii", undecl[0])
                self.error = True
            undecl = p[9].look_for_undeclared_procedures()
            l = p[1]
            p[0] = p[9]

    def p_procedures_empty(self,p):
        'procedures :'
        pass


    def p_main_var(self,p):
        'main : PROGRAM IS VAR declarations BEGIN commands END'
        #p[0] = 'PROGRAM IS\nVAR ' + str(p[4]) + '\nBEGIN\n' + str(p[6]) + '\nEND'
        #print(p[4])
        p[6] = self.delete_useless_assigns(p[4],p[6])
        p[6].look_for_uninit_variables(p[4])
        p[0] = self.store_local_variables('MAIN',p[4], p[6],p.lineno(3))
        undecl = p[0].look_for_undeclared_variables()
        if (undecl[0] != -1):
            print("Błąd - niezadeklarowana zmienna " + undecl[1] + " użyta w linii", undecl[0])
            self.error = True
        undecl = p[0].look_for_undeclared_procedures()
        p[0].add_procedure_location('MAIN')

    def p_main_novar(self,p):
        'main : PROGRAM IS BEGIN commands END'
        p[0] = p[4]
        p[0].add_procedure_location('MAIN')


    def p_commands_ex(self,p):
        'commands : commands command'
        p[1].merge(p[2])
        p[0] = p[1]

    def p_commands_noex(self,p):
        'commands : command'
        p[0] = p[1]


    def p_command_assign(self,p):
        'command : ID ASSIGN expression SC'
        l = p[3]
        l.add_line('STORE V' + str(p[1]),p.lineno(1))
        l.append_to_all_lines('[@store ' + str(p[1]) +']')
        p[0] = l

    def p_command_ifelse(self,p):
        'command : IF condition THEN commands ELSE commands ENDIF'
        l = p[2]
        l.add_line('JZERO LINE+' + str(len(p[4].lines)+2), p.lineno(1))
        l.merge(p[4])
        l.add_line('JUMP LINE+' + str(len(p[6].lines)+1), p.lineno(1))
        l.merge(p[6])
        p[0] = l

    def p_command_if(self,p):
        'command : IF condition THEN commands ENDIF'
        l = p[2]
        l.add_line('JZERO LINE+' + str(len(p[4].lines)+1),p.lineno(1))
        l.merge(p[4])
        p[0] = l

    def p_command_while(self,p):
        'command : WHILE condition DO commands ENDWHILE'
        l = p[2]
        l.add_line('JZERO LINE+' + str(len(p[4].lines)+2),p.lineno(1))
        l.merge(p[4])
        l.add_line('JUMP LINE-' + str(len(p[2].lines)),p.lineno(1))
        p[0] = l

    def p_command_repeat(self,p):
        'command : REPEAT commands UNTIL condition SC'
        l = p[2]
        l.merge(p[4])
        l.add_line('JZERO LINE-' + str(len(p[2].lines)),p.lineno(1))
        p[0] = l


    def p_command_head(self,p):
        'command : prochead_exec SC'
        p[0] = p[1]

    def p_command_read(self,p):
        'command : READ ID SC'
        l = EnumeratedString()
        l.add_line('GET V' + p[2],p.lineno(1))
        p[0] = l

    def p_command_write_num(self,p):
        'command : WRITE NUMBER SC'
        v1 = str(p[2])
        l = EnumeratedString()
        l.add_line('PUT ' + str(self.remember_number(v1)),p.lineno(1))
        p[0] = l

    def p_command_write_id(self,p):
        'command : WRITE ID SC'
        v1 = str(p[2])
        l = EnumeratedString()
        l.add_line('PUT ' + 'V' + v1,p.lineno(1))
        p[0] = l
    
    def p_prochead_exec(self,p):
        'prochead_exec : ID OP declarations_exec CP'
        arg_list = p[3]
        proc_name = p[1]
        l = EnumeratedString()
        for i in range(len(arg_list)):
            l.add_line('SET V' + arg_list[i],p.lineno(1)) # pointer -> LOAD, local -> SET
            l.add_line('STORE ' + proc_name + '#' + str(i),p.lineno(1))
        l.add_line('SET LINE+3',p.lineno(1))
        l.add_line('STORE ' + proc_name + '#' + str(len(arg_list)),p.lineno(1))
        #l.add_line('STORE ' + proc_name + '#JUMPI')
        l.add_line('JUMP ' + proc_name,p.lineno(1))
        p[0] = l
        
    
    def p_declarations_comma_exec(self,p):
        'declarations_exec : declarations_exec COMMA ID'
        p[0] = list(p[1]) +[str(p[3])]

    def p_declarations_comma(self,p):
        'declarations : declarations COMMA ID'
        p[0] = list(p[1]) +[str(p[3])]

    def p_declarations_exec(self,p):
        'declarations_exec : ID'
        p[0] = [str(p[1])]

    def p_declarations(self,p):
        'declarations : ID'
        p[0] = [str(p[1])]



    def p_expression_add_num_id(self,p):
        'expression : NUMBER ADD ID'
        v1 = str(p[1])
        v2 = str(p[3])
        l = EnumeratedString()
        l.add_line('SET ' + v1, p.lineno(1))
        l.add_line('ADD ' + 'V' + v2, p.lineno(1))
        p[0] = l
    def p_expression_add_id_num(self,p):
        'expression : ID ADD NUMBER'
        v1 = str(p[1])
        v2 = str(p[3])
        l = EnumeratedString()
        l.add_line('SET ' + v2, p.lineno(1))
        l.add_line('ADD ' + 'V' + v1, p.lineno(1))
        p[0] = l
    def p_expression_add_id_id(self,p):
        'expression : ID ADD ID'
        v1 = str(p[1])
        v2 = str(p[3])
        l = EnumeratedString()
        l.add_line('LOAD ' + 'V' + v1, p.lineno(1))
        l.add_line('ADD ' + 'V' + v2, p.lineno(1))
        p[0] = l
    def p_expression_add_num_num(self,p):
        'expression : NUMBER ADD NUMBER'
        v1 = str(p[1])
        v2 = str(p[3])
        l = EnumeratedString()
        l.add_line('SET ' + v1, p.lineno(1))
        l.add_line('ADD ' + str(self.remember_number(int(v2))), p.lineno(1))
        p[0] = l
    


    def p_expression_sub_num_id(self,p):
        'expression : NUMBER SUB ID'
        v1 = str(p[1])
        v2 = str(p[3])
        l = EnumeratedString()
        l.add_line('SET ' + v1, p.lineno(1))
        l.add_line('SUB ' + 'V' + v2, p.lineno(1))
        p[0] = l
    def p_expression_sub_id_num(self,p):
        'expression : ID SUB NUMBER'
        v1 = str(p[1])
        v2 = str(self.remember_number(int(p[3])))
        l = EnumeratedString()
        l.add_line('LOAD V' + v1, p.lineno(1))
        l.add_line('SUB ' + v2, p.lineno(1))
        p[0] = l
    def p_expression_sub_id_id(self,p):
        'expression : ID SUB ID'
        v1 = str(p[1])
        v2 = str(p[3])
        l = EnumeratedString()
        l.add_line('LOAD ' + 'V' + v1, p.lineno(1))
        l.add_line('SUB ' + 'V' + v2, p.lineno(1))
        p[0] = l
    def p_expression_sub_num_num(self,p):
        'expression : NUMBER SUB NUMBER'
        v1 = str(p[1])
        v2 = str(p[3])
        l = EnumeratedString()
        l.add_line('SET ' + v1, p.lineno(1))
        l.add_line('SUB ' + str(self.remember_number(int(v2))), p.lineno(1))
        p[0] = l
    def p_expression_mul_id_id(self,p):
        'expression : ID MUL ID'
        self.multiplication = True
        v1 = 'V' + str(p[1])
        v2 = 'V' + str(p[3])
        l = EnumeratedString()
        l.add_line('LOAD ' + v2, p.lineno(1))
        l.add_line('STORE 3', p.lineno(1))
        l.add_line('SET LINE+4', p.lineno(1))
        l.add_line('STORE 6', p.lineno(1))
        l.add_line('LOAD ' + v1, p.lineno(1)) # a -2, b -3
        l.add_line('JUMP MULTIPLICATION', p.lineno(1))
        p[0] = l
    def p_expression_mul_id_num(self,p):
        'expression : ID MUL NUMBER'
        v1 = 'V' + str(p[1])
        v2 = str(p[3])
        v2n = int(p[3])
        l = EnumeratedString()
        if (is_power_of_two(v2n)):
            l.add_line('LOAD ' + v1, p.lineno(1))
            while(v2n > 1):
                l.add_line('ADD 0', p.lineno(1))
                v2n /= 2
        else:
            self.multiplication = True
            l.add_line('SET ' + v2, p.lineno(1))
            l.add_line('STORE 3', p.lineno(1))
            l.add_line('SET LINE+4', p.lineno(1))
            l.add_line('STORE 6', p.lineno(1))
            l.add_line('LOAD ' + v1, p.lineno(1)) # a -2, b -3
            l.add_line('JUMP MULTIPLICATION', p.lineno(1))
        p[0] = l
    def p_expression_mul_num_id(self,p):
        'expression : NUMBER MUL ID'
        v1 = str(p[1])
        v2 = 'V' + str(p[3])
        v1n = int(p[1])
        l = EnumeratedString()
        if (is_power_of_two(v1n)):
            l.add_line('LOAD ' + v2, p.lineno(1))
            while(v1n > 1):
                l.add_line('ADD 0', p.lineno(1))
                v1n /= 2
        else:
            self.multiplication = True
            l.add_line('LOAD ' + v2, p.lineno(1))
            l.add_line('STORE 3', p.lineno(1))
            l.add_line('SET LINE+4', p.lineno(1))
            l.add_line('STORE 6', p.lineno(1))
            l.add_line('SET ' + v1, p.lineno(1)) # a -2, b -3
            l.add_line('JUMP MULTIPLICATION', p.lineno(1))
        p[0] = l
    def p_expression_mul_num_num(self,p):
        'expression : NUMBER MUL NUMBER'
        self.multiplication = True
        v1 = str(p[1])
        v2 = str(p[3])
        v2n = int(p[3])
        v1n = int(p[1])
        l = EnumeratedString()
        if (is_power_of_two(v1n)):
            l.add_line('SET ' + v2, p.lineno(1))
            while(v1n > 1):
                l.add_line('ADD 0', p.lineno(1))
                v1n /= 2
        elif ((is_power_of_two(v2n))):
            l.add_line('SET ' + v1, p.lineno(1))
            while(v2n > 1):
                l.add_line('ADD 0', p.lineno(1))
                v2n /= 2
        else:
            l.add_line('SET ' + v2, p.lineno(1))
            l.add_line('STORE 3', p.lineno(1))
            l.add_line('SET LINE+4', p.lineno(1))
            l.add_line('STORE 6', p.lineno(1))
            l.add_line('SET ' + v1, p.lineno(1)) # a -2, b -3
            l.add_line('JUMP MULTIPLICATION', p.lineno(1))
        p[0] = l


    def p_expression_div_id_id(self,p):
        'expression : ID DIV ID'
        v1 = 'V' + str(p[1])
        v2 = 'V' + str(p[3])
        l = EnumeratedString()
        self.division = True
        l.add_line('LOAD ' + v1, p.lineno(1))
        l.add_line('STORE 5', p.lineno(1))
        l.add_line('LOAD ' + v2, p.lineno(1))
        l.add_line('STORE 7', p.lineno(1))
        l.add_line('JZERO LINE+4', p.lineno(1))
        l.add_line('SET LINE+2', p.lineno(1))
        l.add_line('JUMP DIVISION', p.lineno(1))
        l.add_line('LOAD 2', p.lineno(1))
        p[0] = l
    def p_expression_div_id_num(self,p):
        'expression : ID DIV NUMBER'
        l = EnumeratedString()
        v1 = 'V' + str(p[1])
        v2n = int(p[3])
        if (is_power_of_two(v2n)):
            l.add_line('LOAD ' + v1, p.lineno(1))
            while(v2n > 1):
                l.add_line('HALF', p.lineno(1))
                v2n /= 2
        elif (v2n == 0):
            l.add_line('SET 0', p.lineno(1))
        else:
            self.division = True
            l.add_line('SET ' + str(v2n), p.lineno(1))
            l.add_line('STORE 7', p.lineno(1))
            l.add_line('LOAD ' + v1, p.lineno(1))
            l.add_line('STORE 5', p.lineno(1))
            l.add_line('SET LINE+2', p.lineno(1))
            l.add_line('JUMP DIVISION', p.lineno(1))
            l.add_line('LOAD 2', p.lineno(1))
        p[0] = l
    def p_expression_div_num_id(self,p):
        'expression : NUMBER DIV ID'
        v1 = str(self.remember_number(int(p[1])))
        v2 = 'V' + str(p[3])
        l = EnumeratedString()
        self.division = True
        l.add_line('LOAD ' + v2, p.lineno(1))
        l.add_line('JZERO LINE+7', p.lineno(1))
        l.add_line('STORE 7', p.lineno(1))
        l.add_line('LOAD ' + v1, p.lineno(1))
        l.add_line('STORE 5', p.lineno(1))
        l.add_line('SET LINE+2', p.lineno(1))
        l.add_line('JUMP DIVISION', p.lineno(1))
        l.add_line('LOAD 2', p.lineno(1))
        p[0] = l
    def p_expression_div_num_num(self,p):
        'expression : NUMBER DIV NUMBER'
        v1 = str(self.remember_number(int(p[1])))
        v2 = str(self.remember_number(int(p[3])))
        l = EnumeratedString()
        self.division = True
        l.add_line('LOAD ' + v2, p.lineno(1))
        l.add_line('JZERO LINE+7', p.lineno(1))
        l.add_line('STORE 7', p.lineno(1))
        l.add_line('LOAD ' + v1, p.lineno(1))
        l.add_line('STORE 5', p.lineno(1))
        l.add_line('SET LINE+2', p.lineno(1))
        l.add_line('JUMP DIVISION', p.lineno(1))
        l.add_line('LOAD 2', p.lineno(1))
        p[0] = l

    def p_expression_mod_id_id(self,p):
        'expression : ID MOD ID'
        v1 = 'V' + str(p[1])
        v2 = 'V' + str(p[3])
        l = EnumeratedString()
        self.modulo = True
        l.add_line('LOAD ' + v2, p.lineno(1))
        l.add_line('JZERO LINE+7', p.lineno(1))
        l.add_line('STORE 7', p.lineno(1))
        l.add_line('LOAD ' + v1, p.lineno(1))
        l.add_line('STORE 5', p.lineno(1))
        l.add_line('SET LINE+2', p.lineno(1))
        l.add_line('JUMP MODULO', p.lineno(1))
        l.add_line('LOAD 3', p.lineno(1))
        p[0] = l
    def p_expression_mod_id_num(self,p):
        'expression : ID MOD NUMBER'
        v1 = 'V' + str(p[1])
        v2 = str(p[3])
        l = EnumeratedString()
        if (int(p[3]) == 2):
            l.add_line('LOAD ' + v1, p.lineno(1))
            l.add_line('HALF', p.lineno(1))
            l.add_line('STORE 2', p.lineno(1))
            l.add_line('SET 1', p.lineno(1))
            l.add_line('ADD ' + v1, p.lineno(1))
            l.add_line('HALF', p.lineno(1))
            l.add_line('SUB 2', p.lineno(1))
        else:
            self.modulo = True
            l.add_line('SET ' + v2, p.lineno(1))
            l.add_line('JZERO LINE+7', p.lineno(1))
            l.add_line('STORE 7', p.lineno(1))
            l.add_line('LOAD ' + v1, p.lineno(1))
            l.add_line('STORE 5', p.lineno(1))
            l.add_line('SET LINE+2', p.lineno(1))
            l.add_line('JUMP MODULO', p.lineno(1))
            l.add_line('LOAD 3', p.lineno(1))
        p[0] = l
    def p_expression_mod_num_id(self,p):
        'expression : NUMBER MOD ID'
        v1 = str(p[1])
        v2 = 'V' + str(p[3])
        l = EnumeratedString()
        self.modulo = True
        l.add_line('LOAD ' + v2, p.lineno(1))
        l.add_line('JZERO LINE+7', p.lineno(1))
        l.add_line('STORE 7', p.lineno(1))
        l.add_line('SET ' + v1, p.lineno(1))
        l.add_line('STORE 5', p.lineno(1))
        l.add_line('SET LINE+2', p.lineno(1))
        l.add_line('JUMP MODULO', p.lineno(1))
        l.add_line('LOAD 3', p.lineno(1))
        p[0] = l
    def p_expression_mod_num_num(self,p):
        'expression : NUMBER MOD NUMBER'
        v1 = str(p[1])
        v2 = str(p[3])
        l = EnumeratedString()
        self.modulo = True
        l.add_line('SET ' + v2, p.lineno(1))
        l.add_line('JZERO LINE+7', p.lineno(1))
        l.add_line('STORE 7', p.lineno(1))
        l.add_line('SET ' + v1, p.lineno(1))
        l.add_line('STORE 5', p.lineno(1))
        l.add_line('SET LINE+2', p.lineno(1))
        l.add_line('JUMP MODULO', p.lineno(1))
        l.add_line('LOAD 3', p.lineno(1))
        p[0] = l

    def p_expression_num(self,p):
        'expression : NUMBER'
        l = EnumeratedString()
        l.add_line('SET ' + str(p[1]), p.lineno(1))
        p[0] = l

    def p_expression_id(self,p):
        'expression : ID'
        l = EnumeratedString()
        l.add_line('LOAD V' + p[1], p.lineno(1))
        p[0] = l 

    def p_condition_eq_two(self,p):
        'condition : ID EQ NUMBER'
        v1 = 'V' + p[1]
        l = EnumeratedString()
        if (int(p[3]) == 0):
            l.add_line('LOAD ' + v1, p.lineno(2))
            l.add_line('JPOS LINE+3', p.lineno(2))
            l.add_line('SET 1', p.lineno(2))
            l.add_line('JUMP LINE+2', p.lineno(2))
            l.add_line('SET 0', p.lineno(2))
        else:
            
            v2 = str(self.remember_number(str(p[3])))
            
            l.add_line('LOAD ' + v1, p.lineno(2))
            l.add_line('SUB ' + v2, p.lineno(2))
            l.add_line('JPOS LINE+6', p.lineno(2))
            l.add_line('LOAD ' + v2, p.lineno(2))
            l.add_line('SUB ' + v1, p.lineno(2))
            l.add_line('JPOS LINE+3', p.lineno(2))
            l.add_line('SET 1', p.lineno(2))
            l.add_line('JUMP LINE+2', p.lineno(2))
            l.add_line('SET 0', p.lineno(2))
        p[0] = l

    def p_condition_eq_three(self,p):
        'condition : NUMBER EQ ID'
        v1 = 'V' + p[3]
        l = EnumeratedString()
        if (int(p[1]) == 0):
            l.add_line('LOAD ' + v1, p.lineno(2))
            l.add_line('JPOS LINE+3', p.lineno(2))
            l.add_line('SET 1', p.lineno(2))
            l.add_line('JUMP LINE+2', p.lineno(2))
            l.add_line('SET 0', p.lineno(2))
        else:
            
            v2 = str(self.remember_number(str(p[1])))
            
            l.add_line('LOAD ' + v1, p.lineno(2))
            l.add_line('SUB ' + v2, p.lineno(2))
            l.add_line('JPOS LINE+6', p.lineno(2))
            l.add_line('LOAD ' + v2, p.lineno(2))
            l.add_line('SUB ' + v1, p.lineno(2))
            l.add_line('JPOS LINE+3', p.lineno(2))
            l.add_line('SET 1', p.lineno(2))
            l.add_line('JUMP LINE+2', p.lineno(2))
            l.add_line('SET 0', p.lineno(2))
        p[0] = l
    def p_condition_eq_four(self,p):
        'condition : NUMBER EQ NUMBER'
        l = EnumeratedString()
        if (int(p[1]) == int(p[3])):
            l.add_line('SET 1', p.lineno(2))
        else:
            l.add_line('SET 0', p.lineno(2))
        p[0] = l

    # akumulator 0 - false, smthing else - true
    def p_condition_eq(self,p):
        'condition : ID EQ ID'
        v1 = 'V' + str(p[1])
        v2 = 'V' + str(p[3])
        l = EnumeratedString()
        l.add_line('LOAD ' + v1, p.lineno(2))
        l.add_line('SUB ' + v2, p.lineno(2))
        l.add_line('JPOS LINE+6', p.lineno(2))
        l.add_line('LOAD ' + v2, p.lineno(2))
        l.add_line('SUB ' + v1, p.lineno(2))
        l.add_line('JPOS LINE+3', p.lineno(2))
        l.add_line('SET 1', p.lineno(2))
        l.add_line('JUMP LINE+2', p.lineno(2))
        l.add_line('SET 0', p.lineno(2))
        p[0] = l
    
    def p_condition_neq_nn(self,p):
        'condition : NUMBER NEQ NUMBER'
        l = EnumeratedString()
        if (int(p[1]) != int(p[3])):
            l.add_line('SET 1', p.lineno(2))
        else:
            l.add_line('SET 0', p.lineno(2))
        p[0] = l

    def p_condition_neq_in(self,p):
        'condition : ID NEQ NUMBER'
        v1 = 'V' + str(p[1])
        l = EnumeratedString()
        if (int(p[3]) == 0):
            l.add_line('LOAD ' + v1, p.lineno(2))
        else:
            
            v2 = str(self.remember_number(str(p[3])))
            
            l.add_line('LOAD ' + v1, p.lineno(2))
            l.add_line('SUB ' + v2, p.lineno(2))
            l.add_line('JPOS LINE+3', p.lineno(2))
            l.add_line('LOAD ' + v2, p.lineno(2))
            l.add_line('SUB ' + v1, p.lineno(2))
        p[0] = l
        
    def p_condition_neq_ni(self,p):
        'condition : NUMBER NEQ ID'
        v2 = 'V' + str(p[3])
        l = EnumeratedString()
        if (int(p[1]) == 0):
            l.add_line('LOAD ' + v2, p.lineno(2))
        else:
            
            v1 = str(self.remember_number(str(p[1])))
            
            l.add_line('LOAD ' + v1, p.lineno(2))
            l.add_line('SUB ' + v2, p.lineno(2))
            l.add_line('JPOS LINE+3', p.lineno(2))
            l.add_line('LOAD ' + v2, p.lineno(2))
            l.add_line('SUB ' + v1, p.lineno(2))
        p[0] = l

    def p_condition_neq_ii(self,p):
        'condition : ID NEQ ID'
        v1 = 'V' + str(p[1])
        v2 = 'V' + str(p[3])
        l = EnumeratedString()
        l.add_line('LOAD ' + v1, p.lineno(2))
        l.add_line('SUB ' + v2, p.lineno(2))
        l.add_line('JPOS LINE+3', p.lineno(2))
        l.add_line('LOAD ' + v2, p.lineno(2))
        l.add_line('SUB ' + v1, p.lineno(2))
        p[0] = l

    def p_condition_low_nn(self,p):
        'condition : NUMBER LOW NUMBER'
        l = EnumeratedString()
        if (int(p[1]) < int(p[3])):
            l.add_line('SET 1', p.lineno(2))
        else:
            l.add_line('SET 0', p.lineno(2))
        p[0] = l

    def p_condition_low_in(self,p):
        'condition : ID LOW NUMBER'
        v1 = 'V' + str(p[1])
        l = EnumeratedString()
        l.add_line('SET ' + str(p[3]), p.lineno(2))
        l.add_line('SUB ' + v1, p.lineno(2))
        p[0] = l

    def p_condition_low_ni(self,p):
        'condition : NUMBER LOW ID'
        l = EnumeratedString()
        v2 = 'V' + str(p[3])
        if (int(p[1]) == 0):
            l.add_line('LOAD ' + v2, p.lineno(2))
        else:
            v1 = str(self.remember_number(str(p[1])))
            l.add_line('LOAD ' + v2, p.lineno(2))
            l.add_line('SUB ' + v1, p.lineno(2))
        p[0] = l

    def p_condition_low_ii(self,p):
        'condition : ID LOW ID'
        v1 = 'V' + str(p[1])
        v2 = 'V' + str(p[3])
        l = EnumeratedString()
        l.add_line('LOAD ' + v2, p.lineno(2))
        l.add_line('SUB ' + v1, p.lineno(2))
        p[0] = l

    def p_condition_gre_nn(self,p):
        'condition : NUMBER GRE NUMBER'
        l = EnumeratedString()
        if (int(p[1]) > int(p[3])):
            l.add_line('SET 1', p.lineno(2))
        else:
            l.add_line('SET 0', p.lineno(2))
        p[0] = l

    def p_condition_gre_in(self,p):
        'condition : ID GRE NUMBER'
        l = EnumeratedString()
        v1 = 'V' + str(p[1])
        if (int(p[3]) == 0):
            l.add_line('LOAD ' + v1, p.lineno(2))
        else:
            v2 = str(self.remember_number(str(p[3]))) 
            
            l.add_line('LOAD ' + v1, p.lineno(2))
            l.add_line('SUB ' + v2, p.lineno(2))
        p[0] = l

    def p_condition_gre_ni(self,p):
        'condition : NUMBER GRE ID'
        v1 = str(p[1])
        v2 = 'V' + str(p[3])
        l = EnumeratedString()
        l.add_line('SET ' + v1, p.lineno(2))
        l.add_line('SUB ' + v2, p.lineno(2))
        p[0] = l

    def p_condition_gre_ii(self,p):
        'condition : ID GRE ID'
        v1 = 'V' + str(p[1])
        v2 = 'V' + str(p[3])
        l = EnumeratedString()
        l.add_line('LOAD ' + v1, p.lineno(2))
        l.add_line('SUB ' + v2, p.lineno(2))
        p[0] = l

    def p_condition_lowo_nn(self,p):
        'condition : NUMBER LOWO NUMBER'
        l = EnumeratedString()
        if (int(p[1]) <= int(p[3])):
            l.add_line('SET 1', p.lineno(2))
        else:
            l.add_line('SET 0', p.lineno(2))
        p[0] = l

    def p_condition_lowo_ni(self,p):
        'condition : NUMBER LOWO ID'
        v1 = str(p[1])
        v2 = 'V' + str(p[3])
        l = EnumeratedString()
        l.add_line('SET ' + v1, p.lineno(2))
        l.add_line('SUB ' + v2, p.lineno(2))
        l.add_line('JPOS LINE+3', p.lineno(2))
        l.add_line('SET 1', p.lineno(2))
        l.add_line('JUMP LINE+2', p.lineno(2))
        l.add_line('SET 0', p.lineno(2))
        p[0] = l

    def p_condition_lowo_in(self,p):
        'condition : ID LOWO NUMBER'
        v1 = 'V' + str(p[1])
        v2 = str(self.remember_number(str(p[3])))
        l = EnumeratedString()
        l.add_line('LOAD ' + v1, p.lineno(2))
        l.add_line('SUB ' + v2, p.lineno(2))
        l.add_line('JPOS LINE+3', p.lineno(2))
        l.add_line('SET 1', p.lineno(2))
        l.add_line('JUMP LINE+2', p.lineno(2))
        l.add_line('SET 0', p.lineno(2))
        p[0] = l

    def p_condition_lowo_ii(self,p):
        'condition : ID LOWO ID'
        v1 = 'V' + str(p[1])
        v2 = 'V' + str(p[3])
        l = EnumeratedString()
        l.add_line('LOAD ' + v1, p.lineno(2))
        l.add_line('SUB ' + v2, p.lineno(2))
        l.add_line('JPOS LINE+3', p.lineno(2))
        l.add_line('SET 1', p.lineno(2))
        l.add_line('JUMP LINE+2', p.lineno(2))
        l.add_line('SET 0', p.lineno(2))
        p[0] = l

    def p_condition_greo_nn(self,p):
        'condition : NUMBER GREO NUMBER'
        l = EnumeratedString()
        if (int(p[1]) >= int(p[3])):
            l.add_line('SET 1', p.lineno(2))
        else:
            l.add_line('SET 0', p.lineno(2))
        p[0] = l
    
    def p_condition_greo_ni(self,p):
        'condition : NUMBER GREO ID'
        v1 = str(self.remember_number(str(p[1])))
        v2 = 'V' + str(p[3])
        l = EnumeratedString()
        l.add_line('LOAD ' + v2, p.lineno(2))
        l.add_line('SUB ' + v1, p.lineno(2))
        l.add_line('JPOS LINE+3', p.lineno(2))
        l.add_line('SET 1', p.lineno(2))
        l.add_line('JUMP LINE+2', p.lineno(2))
        l.add_line('SET 0', p.lineno(2))
        p[0] = l
    
    def p_condition_greo_in(self,p):
        'condition : ID GREO NUMBER'
        v1 = 'V' + str(p[1])
        v2 = str(p[3])
        l = EnumeratedString()
        l.add_line('SET ' + v2, p.lineno(2))
        l.add_line('SUB ' + v1, p.lineno(2))
        l.add_line('JPOS LINE+3', p.lineno(2))
        l.add_line('SET 1', p.lineno(2))
        l.add_line('JUMP LINE+2', p.lineno(2))
        l.add_line('SET 0', p.lineno(2))
        p[0] = l

    def p_condition_greo_ii(self,p):
        'condition : ID GREO ID'
        v1 = 'V' + str(p[1])
        v2 = 'V' + str(p[3])
        l = EnumeratedString()
        l.add_line('LOAD ' + v2, p.lineno(2))
        l.add_line('SUB ' + v1, p.lineno(2))
        l.add_line('JPOS LINE+3', p.lineno(2))
        l.add_line('SET 1', p.lineno(2))
        l.add_line('JUMP LINE+2', p.lineno(2))
        l.add_line('SET 0', p.lineno(2))
        p[0] = l

    def p_error(self, p):
        self.error = True
        l = p.lineno
        print("Błąd gramatyczny w liniach ", str(l-1), "-", str(l))


with open(sys.argv[1]) as file:
    data = file.read()

max_val = pow(2,63)-1

data = reduce_numbers(data, max_val)

parserClass = ParserClass(max_val)
parserClass.comments_on = True
result = str(parserClass.parser.parse(data))

if not parserClass.error:
    f = open(sys.argv[2], "w")
    f.write(result)
    f.close()