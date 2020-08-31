import z3
import tempfile
import random
from ..wire import Input, Output, Register, Const, WireVector
from ..fuzz.aflMutators import int2bin
from ..core import Block
from ..memory import RomBlock, MemBlock

def transfer_to_bin(value, bitwidth):
        return "#b" + int2bin(value, bitwidth)


def translate_to_smt(block, output_file, circle=1, rom_blocks=None): 
    consts = dict()
    '''   2020/8/13
    for wire in list(block.wirevector_subset()):
        if type(wire) == Const:
            # some const is in the form like const_0_1'b1, is this legal operation?
            wire.name = wire.name.split("'").pop(0)
            consts[wire.name] = wire
    '''   
    for log_net in list(block.logic_subset()):
        for t in log_net:
            if t:
                for i in t:
                    if isinstance(i, Const):
                        name = i.name.split("'").pop(0)
                        consts[name] = i

    Declare = []
    # write "Main"
    # node_cntr = 0
    initializedMem = []

    ##################################6/2
    # if there are rom blocks, need to be initialized
    if rom_blocks is not None:
        for x in rom_blocks:
            if x.name not in initializedMem:   
                initializedMem.append(x.name)
                output_file.write("(declare-const %s (Array (_ BitVec %s) (_ BitVec %s)))\n" % (x.name, x.addrwidth, x.bitwidth))
                # if rom data is a function, calculate the data first
                if callable(x.data):
                    romdata = [x.data(i) for i in range(2 ** x.addrwidth)]
                    x.data = romdata
                # write rom block initialization data
                for i in range(len(x.data)):
                    output_file.write("(assert (= (store %s %s %s) %s))\n" % (x.name, transfer_to_bin(i, x.addrwidth), transfer_to_bin(x.data[i], x.bitwidth), x.name))
    ##################################
    if circle == 1:
        for log_net in list(block.logic_subset()):
            if log_net.op == '&':
                if log_net.dests[0].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.dests[0].name, log_net.dests[0].bitwidth))
                    Declare.append(log_net.dests[0].name)
                if log_net.args[0].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.args[0].name, log_net.args[0].bitwidth))
                    Declare.append(log_net.args[0].name)
                if log_net.args[1].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.args[1].name, log_net.args[1].bitwidth))
                    Declare.append(log_net.args[1].name)
                output_file.write("(assert (= %s (bvand %s %s)))\n" % (
                log_net.dests[0].name, log_net.args[0].name, log_net.args[1].name))
            elif log_net.op == '|':
                if log_net.dests[0].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.dests[0].name, log_net.dests[0].bitwidth))
                    Declare.append(log_net.dests[0].name)
                if log_net.args[0].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.args[0].name, log_net.args[0].bitwidth))
                    Declare.append(log_net.args[0].name)
                if log_net.args[1].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.args[1].name, log_net.args[1].bitwidth))
                    Declare.append(log_net.args[1].name)
                output_file.write("(assert (= %s (bvor %s %s)))\n" % (
                log_net.dests[0].name, log_net.args[0].name, log_net.args[1].name))
            elif log_net.op == '^':
                if log_net.dests[0].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.dests[0].name, log_net.dests[0].bitwidth))
                    Declare.append(log_net.dests[0].name)
                if log_net.args[0].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.args[0].name, log_net.args[0].bitwidth))
                    Declare.append(log_net.args[0].name)
                if log_net.args[1].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.args[1].name, log_net.args[1].bitwidth))
                    Declare.append(log_net.args[1].name)
                output_file.write("(assert (= %s (bvxor %s %s)))\n" % (
                log_net.dests[0].name, log_net.args[0].name, log_net.args[1].name))
            elif log_net.op == 'n':
                if log_net.dests[0].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.dests[0].name, log_net.dests[0].bitwidth))
                    Declare.append(log_net.dests[0].name)
                if log_net.args[0].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.args[0].name, log_net.args[0].bitwidth))
                    Declare.append(log_net.args[0].name)
                if log_net.args[1].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.args[1].name, log_net.args[1].bitwidth))
                    Declare.append(log_net.args[1].name)
                output_file.write("(assert (= %s (bvnand %s %s)))\n" % (
                log_net.dests[0].name, log_net.args[0].name, log_net.args[1].name))
            elif log_net.op == '~':
                if log_net.dests[0].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.dests[0].name, log_net.dests[0].bitwidth))
                    Declare.append(log_net.dests[0].name)
                if log_net.args[0].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.args[0].name, log_net.args[0].bitwidth))
                    Declare.append(log_net.args[0].name)
                output_file.write("(assert (= %s (bvnot %s)))\n" % (log_net.dests[0].name, log_net.args[0].name))
            elif log_net.op == '+':
                if log_net.dests[0].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.dests[0].name, log_net.dests[0].bitwidth))
                    Declare.append(log_net.dests[0].name)
                if log_net.args[0].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.args[0].name, log_net.args[0].bitwidth))
                    Declare.append(log_net.args[0].name)
                if log_net.args[1].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.args[1].name, log_net.args[1].bitwidth))
                    Declare.append(log_net.args[1].name)
                a = ''
                for i in range(0, 2):
                    if (log_net.args[i].name in consts) and (log_net.args[i].signed):
                        a = a + " (concat #b1 " + log_net.args[i].name + ") "
                    else:
                        a = a + " ((_ zero_extend 1) " + log_net.args[i].name + ") "

                output_file.write("(assert (= %s (bvadd %s)))\n" % (log_net.dests[0].name, a))
            elif log_net.op == '-':
                if log_net.dests[0].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.dests[0].name, log_net.dests[0].bitwidth))
                    Declare.append(log_net.dests[0].name)
                if log_net.args[0].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.args[0].name, log_net.args[0].bitwidth))
                    Declare.append(log_net.args[0].name)
                if log_net.args[1].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.args[1].name, log_net.args[1].bitwidth))
                    Declare.append(log_net.args[1].name)
                sub = ''
                for i in range(0, 2):
                    if (log_net.args[i].name in consts) and (log_net.args[i].signed):
                        sub = sub + " (concat #b1 " + log_net.args[i].name + ") "
                    else:
                        sub = sub + " ((_ zero_extend 1) " + log_net.args[i].name + ") "

                output_file.write("(assert (= %s (bvsub %s)))\n" % (log_net.dests[0].name, sub))
            elif log_net.op == '*':
                if log_net.dests[0].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.dests[0].name, log_net.dests[0].bitwidth))
                    Declare.append(log_net.dests[0].name)
                if log_net.args[0].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.args[0].name, log_net.args[0].bitwidth))
                    Declare.append(log_net.args[0].name)
                if log_net.args[1].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.args[1].name, log_net.args[1].bitwidth))
                    Declare.append(log_net.args[1].name)
                mul = ''
                for i in range(0, 2):
                    if (log_net.args[i].name in consts) and (log_net.args[i].signed):
                        mu = ''
                        for j in range(0, log_net.args[i].bitwidth):
                            mu = mu + '1'
                        mul = mul + " (concat #b" + mu + " " + log_net.args[i].name + ") "
                    else:
                        mul = mul + " ((_ zero_extend " + str(log_net.args[i].bitwidth) + ") " + log_net.args[
                            i].name + ") "

                output_file.write("(assert (= %s (bvmul %s)))\n" % (log_net.dests[0].name, mul))
            elif log_net.op == '=':
                if log_net.dests[0].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.dests[0].name, log_net.dests[0].bitwidth))
                    Declare.append(log_net.dests[0].name)
                if log_net.args[0].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.args[0].name, log_net.args[0].bitwidth))
                    Declare.append(log_net.args[0].name)
                if log_net.args[1].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.args[1].name, log_net.args[1].bitwidth))
                    Declare.append(log_net.args[1].name)
                output_file.write("(assert (ite (= %s %s) (= %s #b1) (= %s #b0)))\n" % (
                log_net.args[0].name, log_net.args[1].name, log_net.dests[0].name, log_net.dests[0].name))
            elif log_net.op == '<':
                if log_net.dests[0].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.dests[0].name, log_net.dests[0].bitwidth))
                    Declare.append(log_net.dests[0].name)
                if log_net.args[0].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.args[0].name, log_net.args[0].bitwidth))
                    Declare.append(log_net.args[0].name)
                if log_net.args[1].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.args[1].name, log_net.args[1].bitwidth))
                    Declare.append(log_net.args[1].name)
                output_file.write("(assert (ite (bvult %s %s) (= %s #b1) (= %s #b0)))\n" % (
                log_net.args[0].name, log_net.args[1].name, log_net.dests[0].name, log_net.dests[0].name))
            elif log_net.op == '>':
                if log_net.dests[0].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.dests[0].name, log_net.dests[0].bitwidth))
                    Declare.append(log_net.dests[0].name)
                if log_net.args[0].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.args[0].name, log_net.args[0].bitwidth))
                    Declare.append(log_net.args[0].name)
                if log_net.args[1].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.args[1].name, log_net.args[1].bitwidth))
                    Declare.append(log_net.args[1].name)
                output_file.write("(assert (ite (bvugt %s %s) (= %s #b1) (= %s #b0)))\n" % (
                log_net.args[0].name, log_net.args[1].name, log_net.dests[0].name, log_net.dests[0].name))
            elif log_net.op == 'w':
                if log_net.dests[0].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.dests[0].name, log_net.dests[0].bitwidth))
                    Declare.append(log_net.dests[0].name)
                if log_net.args[0].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.args[0].name, log_net.args[0].bitwidth))
                    Declare.append(log_net.args[0].name)
                output_file.write("(assert (= %s %s))\n" % (log_net.dests[0].name, log_net.args[0].name))
            elif log_net.op == 'x':
                if log_net.dests[0].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.dests[0].name, log_net.dests[0].bitwidth))
                    Declare.append(log_net.dests[0].name)
                if log_net.args[0].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.args[0].name, log_net.args[0].bitwidth))
                    Declare.append(log_net.args[0].name)
                if log_net.args[1].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.args[1].name, log_net.args[1].bitwidth))
                    Declare.append(log_net.args[1].name)
                if log_net.args[2].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.args[2].name, log_net.args[2].bitwidth))
                    Declare.append(log_net.args[2].name)
                output_file.write("(assert (ite (= %s #b0) (= %s %s) (= %s %s)))\n" % (
                log_net.args[0].name, log_net.dests[0].name, log_net.args[1].name, log_net.dests[0].name,
                log_net.args[2].name))
            elif log_net.op == 'c':
                if log_net.dests[0].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.dests[0].name, log_net.dests[0].bitwidth))
                    Declare.append(log_net.dests[0].name)
                c = ''
                for i in range(len(log_net.args)):
                    if log_net.args[i].name not in Declare:
                        output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.args[i].name, log_net.args[i].bitwidth))
                        Declare.append(log_net.args[i].name)
                    c = c + ' ' + log_net.args[i].name
                output_file.write("(assert (= %s (concat %s)))\n" % (log_net.dests[0].name, c))
            elif log_net.op == 's':
                if log_net.dests[0].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.dests[0].name, log_net.dests[0].bitwidth))
                    Declare.append(log_net.dests[0].name)
                if log_net.args[0].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.args[0].name, log_net.args[0].bitwidth))
                    Declare.append(log_net.args[0].name)
                string = ''
                extract_item = 0
                for i in log_net.op_param[::-1]:
                    extract_item = extract_item + 1
                    string = string + "((_ extract " + str(i) + " " + str(i) + ")" + " " + log_net.args[0].name + ") "
                if extract_item == 1:
                    output_file.write("(assert (= %s  %s))\n" % (log_net.dests[0].name, string))
                else:
                    output_file.write("(assert (= %s (concat %s)))\n" % (log_net.dests[0].name, string))
            elif log_net.op == 'm':  ########6/2
                if not log_net.op_param[1].name in initializedMem:
                    initializedMem.append(log_net.op_param[1].name)
                    output_file.write("(declare-const %s (Array (_ BitVec %s) (_ BitVec %s)))\n" % (
                    log_net.op_param[1].name, log_net.op_param[1].addrwidth,
                    log_net.op_param[1].bitwidth))
                if log_net.dests[0].name not in Declare:
                    output_file.write(
                        "(declare-const %s (_ BitVec %s))\n" % (log_net.dests[0].name, log_net.dests[0].bitwidth))
                    Declare.append(log_net.dests[0].name)
                if log_net.args[0].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.args[0].name, log_net.args[0].bitwidth))
                    Declare.append(log_net.args[0].name)
                output_file.write("(assert (= (select %s %s) %s))\n" % (
                log_net.op_param[1].name, log_net.args[0].name, log_net.dests[0].name))
                    # node_cntr += 1
            elif log_net.op == '@':
                if not log_net.op_param[1].name in initializedMem:
                    initializedMem.append(log_net.op_param[1].name)
                    output_file.write("(declare-const %s (Array (_ BitVec %s) (_ BitVec %s)))\n" % (
                    log_net.op_param[1].name, log_net.op_param[1].addrwidth,
                    log_net.op_param[1].bitwidth))
                if log_net.args[0].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.args[0].name, log_net.args[0].bitwidth))
                    Declare.append(log_net.args[0].name)
                if log_net.args[1].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.args[1].name, log_net.args[1].bitwidth))
                    Declare.append(log_net.args[1].name)
                if log_net.args[2].name not in Declare:
                    output_file.write("(declare-const %s (_ BitVec %s))\n" % (log_net.args[2].name, log_net.args[2].bitwidth))
                    Declare.append(log_net.args[2].name)
                output_file.write("(assert (ite (= %s #b1) (= (store %s %s %s) %s) (= %s %s)))\n" % (log_net.args[2].name, log_net.op_param[1].name, log_net.args[0].name, log_net.args[1].name, log_net.op_param[1].name, log_net.op_param[1].name, log_net.op_param[1].name))
                # node_cntr += 1
            else:
                pass

    else:
        for cir in range(0, circle):
            for log_net in list(block.logic_subset()):
                if log_net.op == '&':
                    if log_net.dests[0].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.dests[0].name, cir, log_net.dests[0].bitwidth))
                        Declare.append(log_net.dests[0].name + '_' + str(cir))
                    if log_net.args[0].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.args[0].name, cir, log_net.args[0].bitwidth))
                        Declare.append(log_net.args[0].name + '_' + str(cir))
                    if log_net.args[1].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.args[1].name, cir, log_net.args[1].bitwidth))
                        Declare.append(log_net.args[1].name + '_' + str(cir))
                    output_file.write("(assert (= %s_%s (bvand %s_%s %s_%s)))\n" % (log_net.dests[0].name, cir, log_net.args[0].name, cir, log_net.args[1].name, cir))
                elif log_net.op == '|':
                    if log_net.dests[0].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.dests[0].name, cir, log_net.dests[0].bitwidth))
                        Declare.append(log_net.dests[0].name + '_' + str(cir))
                    if log_net.args[0].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.args[0].name, cir, log_net.args[0].bitwidth))
                        Declare.append(log_net.args[0].name + '_' + str(cir))
                    if log_net.args[1].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.args[1].name, cir, log_net.args[1].bitwidth))
                        Declare.append(log_net.args[1].name + '_' + str(cir))
                    output_file.write("(assert (= %s_%s (bvor %s_%s %s_%s)))\n" % (log_net.dests[0].name, cir, log_net.args[0].name, cir, log_net.args[1].name, cir))
                elif log_net.op == '^':
                    if log_net.dests[0].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.dests[0].name, cir, log_net.dests[0].bitwidth))
                        Declare.append(log_net.dests[0].name + '_' + str(cir))
                    if log_net.args[0].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.args[0].name, cir, log_net.args[0].bitwidth))
                        Declare.append(log_net.args[0].name + '_' + str(cir))
                    if log_net.args[1].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.args[1].name, cir, log_net.args[1].bitwidth))
                        Declare.append(log_net.args[1].name + '_' + str(cir))
                    output_file.write("(assert (= %s_%s (bvxor %s_%s %s_%s)))\n" % (log_net.dests[0].name, cir, log_net.args[0].name, cir, log_net.args[1].name, cir))
                elif log_net.op == 'n':
                    if log_net.dests[0].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.dests[0].name, cir, log_net.dests[0].bitwidth))
                        Declare.append(log_net.dests[0].name + '_' + str(cir))
                    if log_net.args[0].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.args[0].name, cir, log_net.args[0].bitwidth))
                        Declare.append(log_net.args[0].name + '_' + str(cir))
                    if log_net.args[1].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.args[1].name, cir, log_net.args[1].bitwidth))
                        Declare.append(log_net.args[1].name + '_' + str(cir))
                    output_file.write("(assert (= %s_%s (bvnand %s_%s %s_%s)))\n" % (log_net.dests[0].name, cir, log_net.args[0].name, cir, log_net.args[1].name, cir))
                elif log_net.op == '~':
                    if log_net.dests[0].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.dests[0].name, cir, log_net.dests[0].bitwidth))
                        Declare.append(log_net.dests[0].name + '_' + str(cir))
                    if log_net.args[0].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.args[0].name, cir, log_net.args[0].bitwidth))
                        Declare.append(log_net.args[0].name + '_' + str(cir))
                    output_file.write("(assert (= %s_%s (bvnot %s_%s)))\n" % (log_net.dests[0].name, cir, log_net.args[0].name, cir))
                elif log_net.op == '+':
                    a = ''
                    for i in range(0, 2):
                        if (log_net.args[i].name in consts) and (log_net.args[i].signed):
                            a = a + " (concat #b1 " + log_net.args[i].name + '_' + str(cir) + ") "
                        else:
                            a = a + " ((_ zero_extend 1) " + log_net.args[i].name + '_' + str(cir) + ") "
                    if log_net.dests[0].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.dests[0].name, cir, log_net.dests[0].bitwidth))
                        Declare.append(log_net.dests[0].name + '_' + str(cir))
                    if log_net.args[0].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.args[0].name, cir, log_net.args[0].bitwidth))
                        Declare.append(log_net.args[0].name + '_' + str(cir))
                    if log_net.args[1].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.args[1].name, cir, log_net.args[1].bitwidth))
                        Declare.append(log_net.args[1].name + '_' + str(cir))
                    output_file.write("(assert (= %s_%s (bvadd %s)))\n" % (log_net.dests[0].name, cir, a))
                elif log_net.op == '-':
                    sub = ''
                    for i in range(0, 2):
                        if (log_net.args[i].name in consts) and (log_net.args[i].signed):
                            sub = sub + " (concat #b1 " + log_net.args[i].name + '_' + str(cir) + ") "
                        else:
                            sub = sub + " ((_ zero_extend 1) " + log_net.args[i].name + '_' + str(cir) + ") "
                    if log_net.dests[0].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.dests[0].name, cir, log_net.dests[0].bitwidth))
                        Declare.append(log_net.dests[0].name + '_' + str(cir))
                    if log_net.args[0].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.args[0].name, cir, log_net.args[0].bitwidth))
                        Declare.append(log_net.args[0].name + '_' + str(cir))
                    if log_net.args[1].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.args[1].name, cir, log_net.args[1].bitwidth))
                        Declare.append(log_net.args[1].name + '_' + str(cir))
                    output_file.write("(assert (= %s_%s (bvsub %s)))\n" % (log_net.dests[0].name, cir, sub))
                elif log_net.op == '*':
                    mul = ''
                    for i in range(0, 2):
                        if (log_net.args[i].name in consts) and (log_net.args[i].signed):
                            mu = ''
                            for j in range(0, log_net.args[i].bitwidth):
                                mu = mu + '1'
                            mul = mul + " (concat #b" + mu + " " + log_net.args[i].name + '_' + str(cir) + ") "
                        else:
                            mul = mul + " ((_ zero_extend " + str(log_net.args[i].bitwidth) + ") " + log_net.args[
                                i].name + '_' + str(cir) + ") "
                    if log_net.dests[0].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.dests[0].name, cir, log_net.dests[0].bitwidth))
                        Declare.append(log_net.dests[0].name + '_' + str(cir))
                    if log_net.args[0].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.args[0].name, cir, log_net.args[0].bitwidth))
                        Declare.append(log_net.args[0].name + '_' + str(cir))
                    if log_net.args[1].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.args[1].name, cir, log_net.args[1].bitwidth))
                        Declare.append(log_net.args[1].name + '_' + str(cir))
                    output_file.write("(assert (= %s_%s (bvmul %s)))\n" % (log_net.dests[0].name, cir, mul))
                elif log_net.op == '=':
                    if log_net.dests[0].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.dests[0].name, cir, log_net.dests[0].bitwidth))
                        Declare.append(log_net.dests[0].name + '_' + str(cir))
                    if log_net.args[0].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.args[0].name, cir, log_net.args[0].bitwidth))
                        Declare.append(log_net.args[0].name + '_' + str(cir))
                    if log_net.args[1].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.args[1].name, cir, log_net.args[1].bitwidth))
                        Declare.append(log_net.args[1].name + '_' + str(cir))
                    output_file.write("(assert (ite (= %s_%s %s_%s) (= %s_%s #b1) (= %s_%s #b0)))\n" % (log_net.args[0].name, cir, log_net.args[1].name, cir, log_net.dests[0].name, cir,
                        log_net.dests[0].name, cir))
                elif log_net.op == '<':
                    if log_net.dests[0].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.dests[0].name, cir, log_net.dests[0].bitwidth))
                        Declare.append(log_net.dests[0].name + '_' + str(cir))
                    if log_net.args[0].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.args[0].name, cir, log_net.args[0].bitwidth))
                        Declare.append(log_net.args[0].name + '_' + str(cir))
                    if log_net.args[1].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.args[1].name, cir, log_net.args[1].bitwidth))
                        Declare.append(log_net.args[1].name + '_' + str(cir))
                    output_file.write("(assert (ite (bvult %s_%s %s_%s) (= %s_%s #b1) (= %s_%s #b0)))\n" % (log_net.args[0].name, cir, log_net.args[1].name, cir, log_net.dests[0].name, cir,
                        log_net.dests[0].name, cir))
                elif log_net.op == '>':
                    if log_net.dests[0].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.dests[0].name, cir, log_net.dests[0].bitwidth))
                        Declare.append(log_net.dests[0].name + '_' + str(cir))
                    if log_net.args[0].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.args[0].name, cir, log_net.args[0].bitwidth))
                        Declare.append(log_net.args[0].name + '_' + str(cir))
                    if log_net.args[1].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.args[1].name, cir, log_net.args[1].bitwidth))
                        Declare.append(log_net.args[1].name + '_' + str(cir))
                    output_file.write("(assert (ite (bvugt %s_%s %s_%s) (= %s_%s #b1) (= %s_%s #b0)))\n" % (log_net.args[0].name, cir, log_net.args[1].name, cir, log_net.dests[0].name, cir,
                        log_net.dests[0].name, cir))
                elif log_net.op == 'w':
                    if log_net.dests[0].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.dests[0].name, cir, log_net.dests[0].bitwidth))
                        Declare.append(log_net.dests[0].name + '_' + str(cir))
                    if log_net.args[0].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.args[0].name, cir, log_net.args[0].bitwidth))
                        Declare.append(log_net.args[0].name + '_' + str(cir))
                    output_file.write("(assert (= %s_%s %s_%s))\n" % (log_net.dests[0].name, cir, log_net.args[0].name, cir))
                elif log_net.op == 'x':
                    if log_net.dests[0].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.dests[0].name, cir, log_net.dests[0].bitwidth))
                        Declare.append(log_net.dests[0].name + '_' + str(cir))
                    if log_net.args[0].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.args[0].name, cir, log_net.args[0].bitwidth))
                        Declare.append(log_net.args[0].name + '_' + str(cir))
                    if log_net.args[1].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.args[1].name, cir, log_net.args[1].bitwidth))
                        Declare.append(log_net.args[1].name + '_' + str(cir))
                    if log_net.args[2].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.args[2].name, cir, log_net.args[2].bitwidth))
                        Declare.append(log_net.args[2].name + '_' + str(cir))
                    output_file.write("(assert (ite (= %s_%s #b0) (= %s_%s %s_%s) (= %s_%s %s_%s)))\n" % (log_net.args[0].name, cir, log_net.dests[0].name, cir, log_net.args[1].name, cir,log_net.dests[0].name, cir, log_net.args[2].name, cir))
                elif log_net.op == 'c':
                    if log_net.dests[0].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.dests[0].name, cir, log_net.dests[0].bitwidth))
                        Declare.append(log_net.dests[0].name + '_' + str(cir))
                    c = ''
                    for i in range(len(log_net.args)):
                        if log_net.args[i].name + '_' + str(cir) not in Declare:
                            output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (log_net.args[i].name, str(cir), log_net.args[i].bitwidth))
                            Declare.append(log_net.args[i].name + '_' + str(cir))
                        c = c + ' ' + log_net.args[i].name + '_' + str(cir)
                    output_file.write("(assert (= %s_%s (concat %s)))\n" % (log_net.dests[0].name, str(cir), c))
                elif log_net.op == 's':
                    string = ''
                    extract_item = 0
                    for i in log_net.op_param[::-1]:
                        extract_item = extract_item + 1
                        string = string + "((_ extract " + str(i) + " " + str(i) + ")" + " " + log_net.args[
                            0].name + '_' + str(cir) + ") "
                    if log_net.dests[0].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.dests[0].name, cir, log_net.dests[0].bitwidth))
                        Declare.append(log_net.dests[0].name + '_' + str(cir))
                    if log_net.args[0].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.args[0].name, cir, log_net.args[0].bitwidth))
                        Declare.append(log_net.args[0].name + '_' + str(cir))
                    if extract_item == 1:
                        output_file.write("(assert (= %s_%s %s))\n" % (log_net.dests[0].name, cir, string))
                    else:
                        output_file.write("(assert (= %s_%s (concat %s)))\n" % (log_net.dests[0].name, cir, string))
                elif log_net.op == 'r':
                    if log_net.dests[0].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.dests[0].name, cir, log_net.dests[0].bitwidth))
                        Declare.append(log_net.dests[0].name + '_' + str(cir))
                    if log_net.args[0].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.args[0].name, cir, log_net.args[0].bitwidth))
                        Declare.append(log_net.args[0].name + '_' + str(cir))
                    if cir == 0:
                        pass
                    else:
                        output_file.write(
                            "(assert (= %s_%s %s_%s))\n" % (log_net.dests[0].name, cir, log_net.args[0].name, cir - 1))
                elif log_net.op == 'm':  #####6/2
                    # mem.append(log_net.op_param[1].name + "_" + str(cir))
                    if log_net.op_param[1].name not in initializedMem:
                        initializedMem.append(log_net.op_param[1].name)
                        output_file.write("(declare-const %s (Array (_ BitVec %s) (_ BitVec %s)))\n" % (
                        log_net.op_param[1].name, log_net.op_param[1].addrwidth,
                        log_net.op_param[1].bitwidth))

                    if log_net.dests[0].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.dests[0].name, cir, log_net.dests[0].bitwidth))
                        Declare.append(log_net.dests[0].name + '_' + str(cir))
                    if log_net.args[0].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.args[0].name, cir, log_net.args[0].bitwidth))
                        Declare.append(log_net.args[0].name + '_' + str(cir))
                    output_file.write("(assert (= (select %s %s_%s) %s_%s))\n" % (log_net.op_param[1].name, log_net.args[0].name, cir, log_net.dests[0].name, cir))
                    # node_cntr += 1
                elif log_net.op == '@':
                    if not log_net.op_param[0] in initializedMem:
                        initializedMem.append(log_net.op_param[0])
                        output_file.write("(declare-const %s (Array (_ BitVec %s) (_ BitVec %s)))\n" % (
                        log_net.op_param[1].name, log_net.op_param[1].addrwidth,
                        log_net.op_param[1].bitwidth))
                    if log_net.args[0].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.args[0].name, cir, log_net.args[0].bitwidth))
                        Declare.append(log_net.args[0].name + '_' + str(cir))
                    if log_net.args[1].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.args[1].name, cir, log_net.args[1].bitwidth))
                        Declare.append(log_net.args[1].name + '_' + str(cir))
                    if log_net.args[2].name + '_' + str(cir) not in Declare:
                        output_file.write("(declare-const %s_%s (_ BitVec %s))\n" % (
                        log_net.args[2].name, cir, log_net.args[2].bitwidth))
                        Declare.append(log_net.args[2].name + '_' + str(cir))

                    output_file.write("(assert (ite (= %s_%s #b1) (= (store %s %s_%s %s_%s) %s)) (= %s %s))\n" % (log_net.args[2].name, cir, log_net.op_param[1].name, log_net.args[0].name, cir, log_net.args[1].name, cir, log_net.op_param[1].name, log_net.op_param[1].name, log_net.op_param[1].name))

                    # node_cntr += 1
                else:
                    pass
    if circle == 1:
        for i in consts:
                if consts[i].signed:
                    con = bin(pow(2, consts[i].bitwidth) - consts[i].val)
                    zero = ""
                    for j in range(0, consts[i].bitwidth - len(con) + 2):
                        zero = zero + "0"
                    output_file.write("(assert (= %s (bvneg %s)))\n" % (consts[i].name, "#b" + zero + con[2:]))
                else:
                    con = bin(consts[i].val)
                    zero = ""
                    for j in range(0, consts[i].bitwidth - len(con) + 2):
                        zero = zero + "0"
                    output_file.write("(assert (= %s %s))\n" % (consts[i].name, "#b" + zero + bin(consts[i].val)[2:]))
    else:
        for cir in range(0, circle):
            for i in consts:
                if consts[i].signed:
                    con = bin(pow(2, consts[i].bitwidth) - consts[i].val)
                    zero = ""
                    for j in range(0, consts[i].bitwidth - len(con) + 2):
                        zero = zero + "0"
                    output_file.write("(assert (= %s_%s (bvneg %s)))\n" % (consts[i].name, cir, "#b" + zero + con[2:]))
                else:
                    con = bin(consts[i].val)
                    zero = ""
                    for j in range(0, consts[i].bitwidth - len(con) + 2):
                        zero = zero + "0"
                    output_file.write("(assert (= %s_%s %s))\n" % (consts[i].name, cir, "#b" + zero + bin(consts[i].val)[2:]))

    return 0

##################################################################
# get inputs for n cycles
##################################################################
def gen_inputs_for_n_cycles(block, n=1):
    inps_cycles = []
    for i in block.wirevector_subset(Input):
        if n == 1:
            inp_cycle = i.name
            inps_cycles.append(inp_cycle)
        else:
            for cycle in range(n):
                inp_cycle = i.name + "_%s" % str(cycle)
                inps_cycles.append(inp_cycle)
    return inps_cycles

def gen_outputs_for_n_cycles(block, n=1):
    otps_cycles = []
    for i in block.wirevector_subset(Output):
        if n == 1:
            otp_cycle = i.name
            otps_cycles.append(otp_cycle)
        else:
            for cycle in range(n):
                otp_cycle = i.name + "_%s" % str(cycle)
                otps_cycles.append(otp_cycle)
    return otps_cycles


def get_value_name(value):
    s = value.split('_')[0:-1]
    if len(s) == 1:
        return s[0]
    else:
        signal = s[0]
        for i in range(1, len(s)):
            signal = signal + '_' + s[i]
        return signal

def get_value_bitwidth(block, value):
    for i in block.wirevector_subset():
        if get_value_name(value) == i.name:
            return i.bitwidth
    print('error: %s is not in block.'%(get_value_name(value)) )
    return 0
# mem=[]
# mux={mux1:[name, bitwith],mux2:...}
# mux_clock = {mux1:[0,1,0,1,...], mux2:[1,0,1,0,...]}
# initial_values={a_0:'0', b_0:'1',...}
def solve_smt(block, mux, mux_clock, cycle, initial_values=None, rom_blocks=None):
    inputs = gen_inputs_for_n_cycles(block, cycle)
    with tempfile.TemporaryFile(mode='w+') as output_file:
        translate_to_smt(block, output_file, cycle, rom_blocks)
        for i in mux:
            if cycle == 1:
                output_file.write("(assert (= %s %s))\n" % (mux[i][0], transfer_to_bin(mux_clock[i][0], mux[i][1])))
            else:
                for c in range(0, cycle):
                    output_file.write("(assert (= %s_%s %s))\n" % (mux[i][0], c, transfer_to_bin(mux_clock[i][c], mux[i][1])))
        if initial_values is None:
            for i in block.wirevector_subset(Register):
                output_file.write("(assert (= %s_0 %s))\n" % (i.name, transfer_to_bin(0, i.bitwidth)))
        else:
            for i in initial_values:
                output_file.write("(assert (= %s %s))\n" % (i, transfer_to_bin(initial_values[i], get_value_bitwidth(block, i))))
        output_file.write("(check-sat)")
        output_file.seek(0)
        l = output_file.read()
        print(l)
        inps = dict()
        otps = dict()
        s = z3.Solver()
        s.add(z3.parse_smt2_string(l))
        if s.check() == z3.sat:
            m = s.model()
            for i in range(0, len(m)):
                if m[i].name() in inputs:
                    inps[m[i].name()] = m[m[i]].as_long()
            for i in inputs:
                if i not in inps:
                    #inps[i] = random.randint(0, 2**get_value_bitwidth(block, i) - 1)
                    inps[i] = 0
            #outputs = gen_outputs_for_n_cycles(block, cycle)
            #for i in range(0, len(m)):
            #    if m[i].name() in outputs:
            #        otps[m[i].name()] = m[m[i]].as_long()
            #print(otps)
            # for i in range(0, len(m)):
               # if m[i].name() in mem:
                   # otps[m[i].name()] = m[m[i]].as_long()
            # print(otps)
            return inps
        elif s.check() == z3.unknown:
            return s.reason_unknown()
        else:
            return {}

            

            
