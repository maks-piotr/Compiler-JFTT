# Author : Maksymilian Piotrowski

import re
import math

def add_numbers(match, max_val):
    input = match.group()
    p = re.compile('\d+')
    l = p.findall(input)
    if (int(l[0]) + int(l[1]) <=  max_val):
        return str(int(l[0]) + int(l[1]))
    return input

def sub_numbers(match, max_val):
    input = match.group()
    p = re.compile('\d+')
    l = p.findall(input)
    return str(max(int(l[0]) - int(l[1]),0))

def mul_numbers(match, max_val):
    input = match.group()
    p = re.compile('\d+')
    l = p.findall(input)
    if (int(l[0]) * int(l[1]) <=  max_val):
        return str(int(l[0]) * int(l[1]))
    return input

def div_numbers(match, max_val):
    input = match.group()
    #print(input)
    p = re.compile('\d+')
    l = p.findall(input)
    if (int(l[1]) == 0):
        return str(0)
    return str(math.floor(int(l[0]) / int(l[1])))

def mod_numbers(match, max_val):
    input = match.group()
    p = re.compile('\d+')
    l = p.findall(input)
    if (int(l[1]) == 0):
        return str(0)
    return str(int(l[0]) % int(l[1]))

def reduce_numbers(input, max_val):
    #print(max_val)
    input = re.sub(r'\d+\+\d+',lambda match: add_numbers(match,max_val), input)
    input = re.sub(r'\d+\-\d+', lambda match: sub_numbers(match,max_val), input)
    input = re.sub(r'\d+\*\d+', lambda match: mul_numbers(match,max_val), input)
    input = re.sub(r'\d+\/\d+', lambda match: div_numbers(match,max_val), input)
    input = re.sub(r'\d+\%\d+', lambda match: mod_numbers(match,max_val), input)
    return input