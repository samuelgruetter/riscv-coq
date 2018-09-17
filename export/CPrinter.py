from LanguagePrinter import LanguagePrinter

type_mappings = {
    'BinNums.Z': 'int',
    'Datatypes.bool': 'bool'
}


def convert_type(t):
    global type_mappings
    res = type_mappings.get(t)
    if res:
        return res
    else:
        return t


class CPrinter(LanguagePrinter):
    def __init__(self, outfile):
        super(CPrinter, self).__init__(outfile)
        self.comment('This C file was autogenerated from Coq')
        self.writeln('#include <stdbool.h>')
        self.end_decl()

    def end_decl(self):
        self.writeln('')

    def comment(self, s):
        self.writeln('// ' + s)

    def type_alias(self, name, rhsName):
        self.writeln('#define {} {}'.format(name, convert_type(rhsName)))
        self.end_decl()

    def enum(self, name, valueNames):
        self.writeln('typedef enum {' + ', '.join(valueNames) + '} ' + name + ';')
        self.end_decl()

    def variant(self, name, branches):
        '''
        name: str
        branches: list of (branchName, typesList) tuples
        '''
        self.enum(name + '_kind', ['K_' + b[0] for b in branches])
        self.writeln('typedef struct {')
        self.increaseIndent()
        self.writeln('{}_kind kind;'.format(name))
        # note: anonymous unions require "-std=c11"
        self.writeln('union {')
        self.increaseIndent()
        for branchName, argTypes in branches:
            self.writeln('struct {')
            self.increaseIndent()
            for i, t in enumerate(argTypes):
                self.writeln('{} f{};'.format(convert_type(t), i))
            self.decreaseIndent()
            self.writeln('} as_' + branchName + ';')
        self.decreaseIndent()
        self.writeln('};')
        self.decreaseIndent()
        self.writeln('} ' + name + ';')
        self.end_decl()

    def begin_constant_decl(self, name, typ):
        self.write('#define ' + name + ' ')

    def end_constant_decl(self):
        self.write('\n')
        self.end_decl()

    def bit_literal(self, s):
        self.write('0b' + s) # gcc extension

    def true_literal(self):
        self.write('true')

    def false_literal(self):
        self.write('false')

    def var(self, varName):
        self.write(varName)

    def begin_fun_decl(self, name, argnamesWithTypes, returnType):
        self.writeln('{} {}({}) {{'.format(convert_type(returnType), name,
            ', '.join([convert_type(tp) + ' ' + argname for argname, tp in argnamesWithTypes])))
        self.increaseIndent()

    def end_fun_decl(self):
        self.write('\n')
        self.decreaseIndent()
        self.writeln('}')
        self.end_decl()

    def begin_match(self, discriminee):
        self.writeln('switch ({}.kind) {{'.format(discriminee))
        self.increaseIndent()

    def end_match(self):
        self.decreaseIndent()
        self.startln()
        self.write('}')

    def begin_match_case(self, discriminee, constructorName, argNames):
        self.writeln('case K_{}:'.format(constructorName))
        self.increaseIndent()
        self.startln()

    def end_match_case(self):
        self.decreaseIndent()
        self.write('\n')

    def begin_match_default_case(self):
        self.writeln('default:')
        self.increaseIndent()
        self.startln()

    def end_match_default_case(self):
        self.decreaseIndent()
        self.write('\n')

    def begin_switch(self, discriminee):
        self.writeln('switch ({}) {{'.format(discriminee))
        self.increaseIndent()

    def end_switch(self):
        self.decreaseIndent()
        self.startln()
        self.write('}')

    def begin_switch_case(self, discriminee, constructorName):
        self.writeln('case {}:'.format(constructorName))
        self.increaseIndent()
        self.startln()

    def end_switch_case(self):
        self.decreaseIndent()
        self.write('\n')

    def begin_switch_default_case(self):
        self.writeln('default:')
        self.increaseIndent()
        self.startln()

    def end_switch_default_case(self):
        self.decreaseIndent()
        self.write('\n')

    def begin_return_expr(self):
        self.write('return ')

    def end_return_expr(self):
        self.write(';')

    def nop(self):
        pass # nothing to be done