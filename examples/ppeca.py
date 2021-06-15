import sys
import string


def replace_return_with_assignment(line):
    return string.replace(line, "return", "/*REPLACED*/output =")

up = False
lines = []

def emit(out, ls):
    global up
    global lines
    out.extend(ls)
    lines = []
    up = False

parencount = 0
decls = [] # global decls
calc_output = [] # calculate_output function body

for line in sys.stdin.readlines():
    ###print 'DEBUG LINE: ',line
    if "calculate_output" in line and line.strip().endswith("{"):
        emit(decls, lines) # flush the decls
    if "int main" in line:
        #print 'flushing calc_output'
        emit(calc_output, map(replace_return_with_assignment, lines)) # flush calculate_output
    for c in line:
        if c == '{':
            up = True
            parencount = parencount + 1
        elif c == '}':
            parencount = parencount - 1
    lines.append(line)
    #print 'SIZE: ', len(lines)

assert(parencount==0)

# here `lines' contains main

# get body of calcelate_output
discard = True
calc_output_chars = []
for line in calc_output:
    for c in line:
        if c == '{':
            parencount = parencount+1
            discard = False
            if parencount == 1:
                continue
        elif c == '}':
            parencount = parencount-1
            if parencount == 0:
                break
        if not discard:
            calc_output_chars.append(c)


assert(parencount==0)



#print '// DLB - decls'
#print ''.join(decls)
#print '********************************************************************************************'

#print 'calc_output'
#print ''.join(''.join(calc_output_chars))
#print '********************************************************************************************'


print '// DLB - main'
#print ''.join(put_decls_in_main())
for line in lines: # main function lines
    if "while" in line:
        print '/*INSERTED decls*/'
        print ''.join(decls),
        print line
    elif "calculate_output" in line:
        print '/*REPLACED calculate_output call*/'
        print ''.join(calc_output_chars),
    else:
        print line,
#print ''.join(lines)
#print '********************************************************************************************'

