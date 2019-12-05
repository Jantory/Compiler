#coding:utf-8
from __future__ import print_function
import os
import re
import copy
from prettytable import *
from LexcialAnalyzer import *
regexs=[
    '{|}|[|]|(|)|,|;|.|?|:'#界符
    ,'++|+|>>=|<<=|>>|<<|--|-|+=|-=|*|*=|%|%=|->|||||||=|/|/=|>|<|>=|<=|==|!=|^=|=|!|~|&&|&|&='#操作符
]
#为节点类型定义一个类
class Node():
    def __init__(self):
        self.place=None
        self.code=[]
        self.asm = []
        self.stack = []
        self.name=None
        self.type = None
        self.data = None
        self.begin=None
        self.end=None
        self.true=None
        self.false=None

'''
符号表和函数表
每次规约识别出一个新的标识符，都会将其加入符号表中，符号的信息包括标识符、
中间变量名、类型、占用空间、内存偏移量、作用的函数等。
而当规约到函数定义的时候，则将函数名、形参列表、代号加入函数表。
'''
class Symbol:
    def __init__(self):
        self.name=None
        self.type=None
        self.size=None
        self.offset=None
        self.place=None
        self.function=None
class FunctionSymbol:
    def __init__(self):
        self.name = None
        self.type = None
        self.lable = None
        self.params = []
def FindSymbol(name, function):
        for item in SymbolTable:
            if item.name==name and item.function == function:
                return item
        return None
#更新符号表
def UpdateSymbolTable(symbol):
    global SymbolTable
    for item in SymbolTable:
        if item.name == symbol.name and item.function == symbol.function:
            SymbolTable.remove(item)
            break
    SymbolTable.append(symbol)
def FindFunctionByName(name):
    for item in FunctionTable:
        if item.name==name:
            return item
    return None
#更新过程表
def UpdateFunctionTable(symbol):
    global FunctionTable
    for item in FunctionTable:
        if item.name == symbol.name:
            FunctionTable.remove(item)
            break
    FunctionTable.append(symbol)
class Production():
    def __init__(self, left, right, position=0, terminals=None):
        self.left=left
        self.right=right
        self.position=position
        self.terminals=terminals
    def Next(self):
        return Production(self.left,
                          self.right,
                          self.position + 1,
                          self.terminals)
    def to_string(self):
        result=self.left+'->'
        position=1
        for data in self.right:
            if position==self.position:
                result += '@'
            result += data['type']+' '
            position += 1
        if position == self.position:
            result += '@'
        result += ',['
        if self.terminals!=None:
            if len(self.terminals)>0:
                for item in sorted(self.terminals):
                    result += '\''+item+'\''+','
                result= result[:-1]
        result += ']'
        return result
    def to_string_compact(self):
        result=self.left+'->'
        for data in self.right:
            result += data['type']+' '
        return result

#定义一个状态类
class State():
    def __init__(self,name):
        self.name=name
        self.productions=[]
        self.string=[]
    def to_string(self):
        for Production in self.productions:
            if Production.to_string() not in self.string:
                self.string.append(Production.to_string())
        return "\n".join(sorted(self.string))
    def get_item(self):
        result=[]
        for production in self.productions:
            expression = production.right
            position = production.position
            if position < len(expression) + 1:
                node = expression[position - 1]
                if node not in result:
                    result.append(node)
        return result
class DFA(object):
    def __init__(self):
        self.state=[]
        self.edge=[]
    def add_state(self, Ix):
        self.state.append(Ix)
    def add_edge(self, Ia, t, Ib):
        self.edge.append((Ia,t,Ib))
def ReadGrammer(file):
    global ProductionGroup
    global TerminalSymbolGroup
    global LeftGroup
    global StartProduction
    type = [
        'seperator', 'operator', 'id', 'STRING', 'CHAR', 'INT', 'FLOAT'
    ]
    LeftGroup.append('S')
    TerminalSymbolGroup.append({'class':'T', 'type': '#'})
    StartProduction = Production('S',[{'class': 'NT', 'type': 'start'}],1, terminals=['#'])
    ProductionGroup.append(StartProduction)
    blocks=open(file).read().split('\n\n')
    LeftGroup=[x.split('\n')[0] for x in blocks]
    for block in blocks:
        lines=block.split('\n')
        left=lines[0]
        expressions=[x.strip(' ')[1:] for x in lines[1:-1]]
        for expression in expressions:
            right=[]
            items=expression.strip(' ').split(' ')
            for item in items:
                data={}
                match=re.match("\'(.+?)\'",item)
                if match:#界符或者操作符
                    for i in range(2):
                        if match.groups()[0] in regexs[i]:
                            data={'class':'T','name':type[i],'type':match.groups()[0]}
                            break
                    if data=={}:
                        data = {'class': 'T', 'type': '$'}
                elif item in type and item !='operator':#基本类型
                    data ={'class':'T','name': item, 'type': item.upper()}
                elif item in Reserved.keys():#保留字
                    data ={'class':'T','name': item, 'type': item}
                else:#非终结符
                     data ={'class':'NT','type':item}
                right.append(data)
                if not data in TerminalSymbolGroup and data['class']!='NT':
                    TerminalSymbolGroup.append(data)
            ProductionGroup.append(Production(left, right, terminals=['#']))
    return
def PrintGrammer(ProductionGroup):
    for Production in ProductionGroup:
        print(Production.to_string_compact())
#在产生式中增加.
def AddDotToproductions(production):
    result=[]
    if len(production.right)==1 and production.right[0]['type']== '$':
        result.append(Production(production.left, production.right, 1))
    else:
        temp=[Production(production.left, production.right, i + 1)
              for i in range(len(production.right) + 1)]
        for item in temp:
            result.append(item)
    return result
def GenerateDotedproductions():
    global DotedProductionGroup
    for P in ProductionGroup:
        for item in AddDotToproductions(P):
            DotedProductionGroup.append(item)
def FindProduction(NT):
    result=[]
    for Production in DotedProductionGroup:
        if Production.left==NT:
            result.append(Production)
    return result
#计算项目集闭包
'''
CLOSURE(I)表示和I中项目可以识别同样活前缀的所有项目的集合。它可以有以下方法得到：
(1)I中的所有项目都属于CLOSURE(I)；
(2)若项目[A→a.Bβ,a]属于CLOSURE(I)，B→ξ是一个产生式，那么，对于FIRST<βa>中的每一个中介符b,
如果[β→.ξ,b]原来不在CLOSURE(I)中，则把它加进去；
(3)重复执行步骤（2），直到CLOSURE(I)不再增大为止。
'''
def CLOSURE(productions):
    def ExpandProduction(production):
        data=[]
        right = production.right
        position = production.position
        terminal = production.terminals
        def get_first_set(node):
            if node['class'] == 'NT':
                return FIRST[next['type']]
            else:
                return GetFirstSet(next['type'])
        if position < len(right) + 1 and right[position - 1]['class'] == 'NT':
            first=[]
            flag=True
            for i in range(position, len(right)):
                next=right[i]
                firstset=copy.deepcopy(get_first_set(next))
                eps={'class':'T','type':'$'}
                if eps in firstset:
                    firstset.remove(eps)
                    for item in firstset:
                        if not item in first:
                            first.append(item)
                else:
                    for item in firstset:
                        if not item in first:
                            first.append(item)
                    flag =False
                    break
            if flag:
                for item in terminal:
                    if not item in first:
                        first.append({'class':'T','type':item})
            productions = FindProduction(right[position - 1]['type'])
            for item in productions:
                if item.position == 1:
                    temp = copy.deepcopy(item)
                    temp.terminals =[item['type'] for item in first]
                    data.append(temp)
        return data
    cache=[p.to_string() for p in productions]
    result=[p for p in productions]
    procession=[p for p in productions]
    while len(procession)>0:
        production=procession.pop()
        data=ExpandProduction(production)
        for item in data:
            if item.to_string() not in cache:
                result.append(item)
                cache.append(item.to_string())
                procession.append(item)
    return result

'''
GO(I,X)=CLOSURE(J)
其中J={任何形如[A→aX.Β,a]的项目[A→a.X.Β,a]属于I}。
'''
def GO(I,item):
    params=[]
    for production in I.productions:
        expression=production.right
        position=production.position
        if position<len(expression)+1:
            node=expression[position-1]
            if node['type']=='$' and len(expression)==1:
                continue
            if node==item and production.Next() not in params:
                params.append(production.Next())
    return CLOSURE(params)
'''
求FIRST集算法
由于文法中产生式非终结符的FIRST集存在相互依赖关系，使用递归法会导致计算量的巨大，
因此我使用了自下而上求解FIRST集依赖的算法:对于每个产生式左侧非终结符T，若其FIRST依赖于另一非终结符F，
则将F加入到其FIRST集中。将所有FIRST集中含有非终结符的非终结符加入到列表Q中，当Q不为空时，
对每个元素进行遍历:若其依赖的非终结符不在Q中，则将其替换为它的FIRST集中的终结符，
当其FIRST集中依赖的非终结符均被替换后，执行出队操作。达到了自底向上求解依赖关系的效果。
'''
def GetFirstSet(symbol):
    global FIRST
    result=[]
    productions=[production for production in ProductionGroup if production.left == symbol]
    if len(productions)==0:
        return [{'class':'T','type':symbol}]
    end_symbol={'class':'T','type':'$'}
    for production in productions:
        right=production.right
        if right==[end_symbol] and end_symbol not in result:
            result.append(end_symbol)
        else:
            cnt = len(right)
            if right[0]['class']=='T' and right[0] not in result:
                result.append(right[0])
                continue
            else:
                if right[0]['type']!=symbol:
                    temp_first=right[0]
                    if temp_first not in result:
                        result.append(temp_first)
            if cnt>1:
                previous=right[0]
                for i in range(1,cnt):
                    if previous['type']!=symbol:
                        if not end_symbol in GetFirstSet(previous['type']):
                            break
                        else:
                            if right[i]['type']!=symbol:
                                temp_first = GetFirstSet(right[i]['type'])
                                if temp_first not in result:
                                    result.append(temp_first[0])
                                previous=right[i]
    FIRST[symbol]=result
    return result
def MakeUpFirst():
    def IsFirstSetComplete(key):
        first = FIRST[key]
        for item in first:
            if item['class'] == 'NT':
                return False
        return True
    global FIRST
    procession =FIRST.keys()
    while len(procession)>0:
        for key in procession:
            first = FIRST[key]
            for item in first:
                if item['class'] == 'NT':
                    if IsFirstSetComplete(item['type']):
                        for value in FIRST[item['type']]:
                            if value not in first:
                                first.append(value)
                        first.remove(item)
            if IsFirstSetComplete(key):
                procession.remove(key)
    return
def GenerateFirst():
    for Nonterminal in LeftGroup:
        GetFirstSet(Nonterminal)
    MakeUpFirst()
    return

'''
建立有限状态自动机DFA、哈希表H、项目集队列P，放入初始项目集I0，存入哈希表中并作为DFA的初始状态。
取出队首元素I，对于I的每个项目X，求I’=GO(I,X)，若I’不在哈希表中，则将其加入P和H中，并添加为DFA新的状态。
为DFA添加一条边(I,X,I’)。循环此操作直到P为空为止，DFA即代表了文法G的LR(1)项目集族，为下一步构造LR(1)分析表提供了依据。
'''
def GenerateDFA():
    global DFA
    def Merge(productions):
        result=[]
        table={}
        reversed={}
        for p in productions:
            temp=Production(p.left,p.right,p.position)
            teiminals = p.terminals
            if not temp.to_string() in table.keys():
                table[temp.to_string()]=teiminals
                reversed[temp.to_string()]=temp
            else:
                for t in teiminals:
                    table[temp.to_string()].append(t)
        for key in table.keys():
            temp=reversed[key]
            temp.terminals=table[key]
            result.append(temp)
        return result
    StateTable={}
    Tranfer=[]
    CurrentState=0
    States=[]
    Procession=[]
    I=State('I'+str(CurrentState))
    I.productions=CLOSURE([StartProduction])
    StateTable[I.name]=I.to_string()
    Procession.append(I)
    DFA.add_state(I)
    States.append(I)
    CurrentState+=1
    while len(Procession)>0:
        I=Procession.pop(0)
        items=I.get_item()
        for item in items:
            temp=State('I'+str(CurrentState))
            temp.productions = Merge(GO(I, item))
            string=temp.to_string()
            if string=='':
                continue
            if string not in StateTable.values():
                States.append(temp)
                StateTable[temp.name] = string
                DFA.add_state(temp)
                DFA.add_edge(I, item, temp)
                Tranfer.append((I.name,item['type'],temp.name))
                Procession.append(temp)
                CurrentState += 1
            else:
                for state in States:
                    if StateTable[state.name] == string:
                        DFA.add_edge(I, item, state)
                        Tranfer.append((I.name, item['type'], state.name))
                        break
    return
def SearchGoToState(I,target):
    for tuple in DFA.edge:
        From, item, To = tuple
        if (From,item)==(I,target):
            return To
    return

'''
(1)若项目[A→·a, b]属于Ik且GO(Ik,a)＝Ij，a为终结符，则置ACTION[k, a]为“sj”。
(2)若项目[A→·a]属于Ik，则置ACTION[k,a]为“rj”；其中假定A→为文法G的第j个产生式。
(3)若项目[S→S·,#]属于Ik，则置ACTION[k,#]为“acc”。
(4)若GO(Ik，A)＝Ij，则置GOTO[k, A]=j。
(5)分析表中凡不能用规则1至4填入信息的空白栏均填上“出错标志”。
'''
def GenerateTable():
    global ACTION
    global GOTO
    global StateIndexTable
    global TerminalIndexTable
    global NonterminalIndexTable
    global Reduce
    global Shift
    ProductionStringGroup =copy.deepcopy(ProductionGroup)
    ProductionStringGroup[0].position=0
    ProductionStringGroup=[p.to_string() for p in ProductionStringGroup]
    states=DFA.state
    edges=DFA.edge
    StateIndexTable = {states[i].name:i for i in range(len(states))}
    TerminalIndexTable = {TerminalSymbolGroup[i]["type"]:i for i in range(len(TerminalSymbolGroup))}
    NonterminalIndexTable = {LeftGroup[i]:i for i in range(len(LeftGroup))}
    ACTION=[["" for x in range(len(TerminalSymbolGroup))] for y in range(len(states))]
    GOTO=[["" for x in range(len(LeftGroup))] for y in range(len(states))]
    for state in states:
        x = StateIndexTable[state.name]
        EndProduction = copy.deepcopy(StartProduction)
        EndProduction.position += 1
        LableGroup=[p.to_string() for p in state.productions]
        if EndProduction.to_string() in LableGroup:
            y = TerminalIndexTable["#"]
            ACTION[x][y] = 'acc'
            continue
        for production in state.productions:
            expression = production.right
            position = production.position
            if position < len(expression) + 1:
                node = expression[position - 1]
                if node['class'] == 'T':
                    y = TerminalIndexTable[node["type"]]
                    To = SearchGoToState(state, node)
                    if node['type'] != '$':
                        index='s'+To.name[1:]
                        if ACTION[x][y] != "" and ACTION[x][y] != index:
                            print("{}包含shift-reduce冲突".format(state.name))
                            print(index, end='->')
                            print(ACTION[x][y])
                            print(state.to_string())
                            print('-------------')
                        ACTION[x][y] = index
                        temp = copy.deepcopy(production)
                        temp.position = 0
                        temp.terminals = ('#')
                        Shift[index] = temp
                    else:
                        for i in range(len(production.terminals)):
                            y = TerminalIndexTable[production.terminals[i]]
                            temp = copy.deepcopy(production)
                            temp.position = 0
                            temp.terminals = ('#')
                            index = 'r' + str(ProductionStringGroup.index(temp.to_string()))
                            if ACTION[x][y] != "" and ACTION[x][y] != index:
                                print("{}包含shift-reduce冲突".format(state.name))
                                print(index, end='->')
                                print(ACTION[x][y])
                                print(state.to_string())
                                print(temp.to_string())
                                print('-------------')
                            ACTION[x][y] = index
                            Reduce[index] = temp

            elif position == len(expression) + 1:
                for i in range(len(production.terminals)):
                    y = TerminalIndexTable[production.terminals[i]]
                    temp=copy.deepcopy(production)
                    temp.position=0
                    temp.terminals=('#')
                    index= 'r'+str(ProductionStringGroup.index(temp.to_string()))
                    if ACTION[x][y]!="" and ACTION[x][y]!=index:
                        print("{}包含shift-reduce冲突".format(state.name))
                        print(index,end='->')
                        print(ACTION[x][y])
                        print(state.to_string())
                        print(temp.to_string())
                        print('-------------')
                    ACTION[x][y] =index
                    Reduce[index] = temp
    for tuple in edges:
        From,item,To=tuple
        if item['class']=='NT':
            x= StateIndexTable[From.name]
            y= NonterminalIndexTable[item['type']]
            if GOTO[x][y] != "" and GOTO[x][y] != To.name:
                print(To.name,end='->')
                print(GOTO[x][y])
                print('-------------')
            GOTO[x][y]=To.name
    return
def PrintTable():
    title=[""]
    for i in range(len(TerminalSymbolGroup)):
        title.append(TerminalSymbolGroup[i]['type'])
    for i in range(len(LeftGroup)):
        title.append(LeftGroup[i])
    temp=title
    title.sort()
    x = PrettyTable(title)
    for i in range(len(DFA.state)):
        row=[DFA.state[i].name]
        for j in range(len(TerminalSymbolGroup)):
            row.append(ACTION[i][j])
        for j in range(len(LeftGroup)):
            row.append(GOTO[i][j])
        x.add_row(row)
    print(x)
    return
def AddTableColum(Operation, Action, State):
    global Table
    global CurrentStep
    CurrentStep += 1
    OpStackColumn = ""
    TokensColumn = ""
    if len([x['type'] for x in OpStack]) > 5:
        OpStackColumn = "...... "
    OpStackColumn += " ".join([x['type'] for x in OpStack][-5:])
    TokensColumn += " ".join([x['type'] for x in Tokens][:5])
    if len([x['type'] for x in Tokens]) > 5:
        TokensColumn += " ......"
    StateStackColumn = " ".join([x.name for x in StateStack])
    row = [str(CurrentStep), OpStackColumn, TokensColumn, Operation, StateStackColumn, Action, State]
    Table.add_row(row)
    return
def MakeAnalyse():
    global OpStack
    global StateStack
    global CurrentProduction
    global Table
    global Tokens
    title=["步骤","当前栈","输入串","动作","状态栈","ACTION","GOTO"]
    Table = PrettyTable(title)
    def FindStateByName(name):
        for state in DFA.state:
            if state.name==name:
                return state
    EndSymbol={'class': 'T', 'type': '#'}
    OpStack=[EndSymbol]
    StateStack=[DFA.state[0]]
    while True:
        CurrentState=StateStack[-1]
        if len(Tokens)==0:
            Token = EndSymbol
        else:
            Token = Tokens[0]
        x = StateIndexTable[CurrentState.name]
        y = TerminalIndexTable[Token['type']]
        Action=ACTION[x][y]
        if Action=='':
            exit(1)
        if Action=='acc':
            Operation = "accept"
            AddTableColum(Operation,Action,"")
            #print(Table)
            print('success!\n')
            break
        elif Action[0]=='s':
            NextState=FindStateByName('I'+Action[1:])
            StateStack.append(NextState)
            Temp =Tokens.pop(0)
            OpStack.append(Temp)
            Operation = "shift"
            AddTableColum(Operation,Action,"")
        elif Action[0]=='r':
            CurrentProduction=Reduce[Action]
            SemanticAnalysis()
            cnt=len(CurrentProduction.right)
            if cnt==1 and CurrentProduction.right[0]['type'] == '$':
                Destination = {'class': 'NT', 'type': CurrentProduction.left}
                CurrentState = StateStack[-1]
                TempState=SearchGoToState(CurrentState, Destination)
                StateStack.append(SearchGoToState(CurrentState, Destination))
                OpStack.append(Destination)
                temp = copy.deepcopy(CurrentProduction)
                temp.position = 0
                Operation = "reduce({})".format(temp.to_string())
                AddTableColum(Operation, Action, TempState.name)
                continue
            for i in range(cnt):
                    item=CurrentProduction.right[cnt-i-1]
                    back = OpStack[-1]
                    if item['class'] != back['class'] and item['type'] != back['type']:
                        print("error in parser place row:{},colum{}".format(Token['row'],Token['colum']))
                        exit(-1)
                    else:
                        OpStack.pop(-1)
                        StateStack.pop(-1)
            CurrentState = StateStack[-1]
            NT=CurrentProduction.left
            x = StateIndexTable[CurrentState.name]
            y = NonterminalIndexTable[NT]
            NextState=FindStateByName(GOTO[x][y])
            StateStack.append(NextState)
            OpStack.append({'class': 'NT', 'type': NT})
            temp = copy.deepcopy(CurrentProduction)
            temp.position = 0
            Operation = "reduce({})".format(temp.to_string())
            AddTableColum(Operation, Action,NextState.name)
    return
def DrawGraph():
    class Graph(object):
        def __init__(self):
            self.edges = []
        def add_edge(self, edge):
            self.edges.append(edge)
        def to_string(self):
            result = "digraph  {\n"
            for edge in self.edges:
                result += "\t{} -> {}\t".format(edge[0], edge[1])
                result += "[constraint = True,\n\t\tlabel = \"{}\",\n\t\tlabelfloat = True];\n".format(edge[2])
            result += "}"
            return result
    GraphView = Graph()
    for tuple in DFA.state:
        From,item,To=tuple
        GraphView.add_edge((From.name,To.name,item['type']))
    with open("temp.dot","w") as f:
        f.write(GraphView.to_string())
    os.system("dot -Tpng temp.dot -o temp.png")
    return
def NewLabel():
    global CurrentLable
    CurrentLable+=1
    return "l"+str(CurrentLable)
def NewFunction():
    global CurrentFunction
    CurrentFunction+=1
    return "f"+str(CurrentFunction)
def NewTemp():
    global CurrentTemp
    CurrentTemp+=1
    return "t"+str(CurrentTemp)

'''
语义栈
LR语义分析是在语法分析的基础上，增加一个语义栈，栈内元素为语义结点。
结点类是S属性文法的表示，判别每次语法分析所使用的产生式，实现不同的语义动作，
每当规约到特定非终结符时，即可产生中间代码。
'''
def SemanticAnalysis():
    LeftExpr=CurrentProduction.left
    RightExpr=CurrentProduction.right
    '''
    中间代码生成
    分为赋值语句、算术运算语句、函数调用语句、
    循环语句、选择语句、跳出语句、函数定义语句等。
    '''
    if LeftExpr=='operator':
        NewNode=Node()
        NewNode.name= 'operator'
        NewNode.type=''
        for i in range(len(RightExpr)):
            Token = OpStack[-(len(RightExpr)-i)]
            NewNode.type += Token['type']
        SemanticStack.append(NewNode)
    elif LeftExpr=='assignment_operator':
        NewNode=Node()
        NewNode.name= 'assignment_operator'
        NewNode.type=[]
        #反向压入语义栈中
        for i in range(len(RightExpr)):
            NewNode.type.append(RightExpr[i]['type'])
        SemanticStack.append(NewNode)
    elif LeftExpr=='type_specifier':
        NewNode=Node()
        NewNode.name= 'type_specifier'
        NewNode.type=RightExpr[0]['type']
        SemanticStack.append(NewNode)
    elif LeftExpr=='primary_expression':
        NewNode=Node()
        if RightExpr[0]['type']=='ID':
            NewNode.data=OpStack[-1]['data']
            TempNode=FindSymbol(NewNode.data, CurrentFunctionSymbol.lable)
            NewNode.place=TempNode.place
            NewNode.type=TempNode.type
        elif RightExpr[0]['type']=='number':
            NewNode.data = OpStack[-1]['data']
            NewNode.type=OpStack[-1]['name'].lower()
        elif RightExpr[1]['type']=='expression':
            NewNode=copy.deepcopy(SemanticStack.pop(-1))
        NewNode.name= 'primary_expression'
        SemanticStack.append(NewNode)
    elif LeftExpr=='arithmetic_expression':
        NewNode=Node()
        NewNode.name= 'arithmetic_expression'
        if len(RightExpr)==1:
            NewNode.stack=[]
        else:
            NewNode=copy.deepcopy(SemanticStack.pop(-1))
            NewNode.stack.insert(0,SemanticStack.pop(-1))
            NewNode.stack.insert(0, SemanticStack.pop(-1))
        SemanticStack.append(NewNode)
    elif LeftExpr=='constant_expression':
        NewNode = SemanticStack.pop(-1)
        NewNode.stack.insert(0, SemanticStack.pop(-1))
        NewNode.name= 'constant_expression'
        if len(NewNode.stack)==1:
            NewNode=copy.deepcopy(NewNode.stack[0])
        else:
            left=NewNode.stack.pop(0)
            while len(NewNode.stack)>0:
                op=NewNode.stack.pop(0)
                right=NewNode.stack.pop(0)
                if left.place==None:
                    arg1=left.data
                else:
                    arg1 =left.place
                if right.place==None:
                    arg2=right.data
                else:
                    arg2 =right.place
                if len(left.code)>0:
                    for code in left.code:
                        NewNode.code.append(code)
                if len(right.code)>0:
                    for code in right.code:
                        NewNode.code.append(code)
                result = Node()
                result.name = 'primary_expression'
                result.place = NewTemp()
                result.type = right.type
                if left.type!=right.type:
                    Token = Tokens[0]
                    print("type error in row{}".format(Token['row']))
                code=(op.type,arg1,arg2,result.place)
                NewNode.code.append(code)
                left=result
                NewNode.type=right.type
            NewNode.place=NewNode.code[-1][3]
        SemanticStack.append(NewNode)
    elif LeftExpr=='declaration_assign':
        NewNode = Node()
        if len(RightExpr)==2:
            name=OpStack[-3]['data']
            NewNode=SemanticStack.pop(-1)
            NewNode.id=name
        else:
            name = OpStack[-1]['data']
            NewNode.id = name
        SemanticStack.append(NewNode)
    elif LeftExpr=='declaration_init':
        NewNode = SemanticStack.pop(-1)
        NewNode.name = 'declaration_init'
        SemanticStack.append(NewNode)
    elif LeftExpr=='declaration_init_list':
        NewNode = Node()
        NewNode.name = 'declaration_init_list'
        if len(RightExpr)==1:
            NewNode.stack=[]
        else:
            NewNode=SemanticStack.pop(-1)
            NewNode.stack.insert(0,SemanticStack.pop(-1))
        SemanticStack.append(NewNode)
    elif LeftExpr=='declaration':
        NewNode = SemanticStack.pop(-1)
        NewNode.stack.insert(0, SemanticStack.pop(-1))
        NewNode.name= 'declaration'
        type=SemanticStack.pop(-1).type
        for node in NewNode.stack:
            symbol = FindSymbol(node.id, CurrentFunctionSymbol.lable)
            if symbol!=None and symbol.function==CurrentFunctionSymbol.lable:
                Token = Tokens[0]
                print("multiple defination of {} in row{}".format(node.id,Token['row']))
            else:
                symbol=Symbol()
            if node.place==None:
                symbol.name=node.id
                symbol.place=NewTemp()
                symbol.type=type
                symbol.function=CurrentFunctionSymbol.lable
                symbol.size = 4
                global CurrentOffset
                symbol.offset = CurrentOffset
                CurrentOffset += symbol.size
                UpdateSymbolTable(symbol)
                if node.data!=None:
                    if(node.type!=type):
                        Token = Tokens[0]
                        print("type error in row{}".format(Token['row']))
                    code=(':=',node.data,'_',symbol.place)
                    NewNode.code.append(code)
            else:
                symbol.name=node.id
                symbol.place=node.place
                symbol.type=type
                symbol.function = CurrentFunctionSymbol.lable
                symbol.size = 4
                #global CurrentOffset
                symbol.offset = CurrentOffset
                CurrentOffset += symbol.size
                UpdateSymbolTable(symbol)
                for code in node.code:
                    NewNode.code.append(code)
        NewNode.stack=[]
        SemanticStack.append(NewNode)
    #赋值语句
    elif LeftExpr=='assignment_expression':
        NewNode = SemanticStack.pop(-1)
        op=SemanticStack.pop(-1)
        name=OpStack[-3]['data']
        symbol = FindSymbol(name, CurrentFunctionSymbol.lable)
        if symbol == None:
            Token = Tokens[0]
            print("none defination of {} in row{}".format(name, Token['row']))
            symbol = Symbol()
            symbol.place=NewTemp()
            symbol.name=name
            symbol.type=NewNode.type
            symbol.function = CurrentFunctionSymbol.lable
            symbol.size=4
            #global CurrentOffset
            symbol.offset=CurrentOffset
            CurrentOffset+=symbol.size
            UpdateSymbolTable(symbol)
        if NewNode.place==None:
            arg=NewNode.data
        else:
            arg = NewNode.place
        if len(op.type)==1:
            code=(':=',arg,'_',symbol.place)
            NewNode.code.append(code)
        else:
            code = (op.type[0], symbol.place, arg, symbol.place)
            NewNode.code.append(code)
        NewNode.name = 'assignment_expression'
        SemanticStack.append(NewNode)
    elif LeftExpr=='assignment_expression_profix':
        NewNode = Node()
        NewNode.name = 'assignment_expression_profix'
        if len(RightExpr)==1:
            NewNode.stack=[]
        else:
            NewNode=SemanticStack.pop(-1)
            NewNode.stack.insert(0,SemanticStack.pop(-1))
        SemanticStack.append(NewNode)
    elif LeftExpr=='assignment_expression_list':
        NewNode = Node()
        NewNode.name = 'assignment_expression_list'
        if len(RightExpr)==1:
            NewNode.stack=[]
        else:
            NewNode=SemanticStack.pop(-1)
            NewNode.stack.insert(0,SemanticStack.pop(-1))
            for node in NewNode.stack:
                for code in reversed(node.code):
                    NewNode.code.insert(0,code)
            NewNode.stack=[]
        SemanticStack.append(NewNode)
    elif LeftExpr=='expression':
        NewNode = SemanticStack.pop(-1)
        NewNode.name = 'expression'
        SemanticStack.append(NewNode)
    elif LeftExpr=='expression_profix':
        NewNode = Node()
        NewNode.name = 'expression_profix'
        if len(RightExpr)==1:
            NewNode.stack=[]
        else:
            NewNode=SemanticStack.pop(-1)
            NewNode.stack.insert(0,SemanticStack.pop(-1))
        SemanticStack.append(NewNode)
    elif LeftExpr=='expression_list':
        NewNode = Node()
        NewNode.name = 'expression_list'
        if len(RightExpr)==1:
            NewNode.stack=[]
        else:
            NewNode=SemanticStack.pop(-1)
            NewNode.stack.insert(0,SemanticStack.pop(-1))
            for node in reversed(NewNode.stack):
                for code in node.code:
                    NewNode.code.insert(0,code)
            #NewNode.stack=[]
        SemanticStack.append(NewNode)
    elif LeftExpr=='expression_statement':
        NewNode = SemanticStack.pop(-1)
        NewNode.name = 'expression_statement'
        SemanticStack.append(NewNode)
    elif LeftExpr=='statement':
        NewNode = SemanticStack.pop(-1)
        NewNode.name = 'statement'
        SemanticStack.append(NewNode)
    elif LeftExpr=='statement_list':
        temp=SemanticStack
        NewNode = Node()
        NewNode.name = 'statement_list'
        if len(RightExpr)==1:
            NewNode.stack=[]
        else:
            NewNode=SemanticStack.pop(-1)
            NewNode.stack.insert(0,SemanticStack.pop(-1))
            for node in NewNode.stack:
                for code in reversed(node.code):
                    NewNode.code.insert(0,code)
            NewNode.stack=[]
        SemanticStack.append(NewNode)
    elif LeftExpr=='compound_statement':
        NewNode = SemanticStack.pop(-1)
        NewNode.name = 'compound_statement'
        SemanticStack.append(NewNode)
    elif LeftExpr=='jump_statement':
        NewNode = Node()
        NewNode.name = 'jump_statement'
        NewNode.type=RightExpr[0]['type']
        if len(RightExpr)==3:
            temp=SemanticStack.pop(-1)
            if temp.place!=None:
                result=temp.place
            else:
                result = temp.data
            NewNode.code.append((':=', result, '_', 'v0'))
            NewNode.code.append(('+', 'sp', 4 * len(CurrentFunctionSymbol.params) + 4, 'sp'))
        NewNode.code.append((NewNode.type, '_', '_', '_'))
        SemanticStack.append(NewNode)
    elif LeftExpr=='selection_statement':
        NewNode = Node()
        NewNode.name = 'selection_statement'
        Node.true=NewLabel()
        Node.false=NewLabel()
        Node.end = NewLabel()
        FalseStmt=SemanticStack.pop(-1)
        TrueStmt = SemanticStack.pop(-1)
        Expression=SemanticStack.pop(-1)
        for code in  Expression.code:
            NewNode.code.append(code)
        NewNode.code.append(('j>',Expression.place,'0',Node.true))
        NewNode.code.append(('j','_','_',Node.false))
        NewNode.code.append((Node.true,':','_','_'))
        for code in TrueStmt.code:
            NewNode.code.append(code)
        NewNode.code.append(('j', '_', '_', Node.end))
        NewNode.code.append((Node.false,':','_','_'))
        for code in FalseStmt.code:
            NewNode.code.append(code)
        NewNode.code.append((Node.end,':','_','_'))
        SemanticStack.append(NewNode)
    elif LeftExpr=='iteration_statement':
        NewNode = Node()
        NewNode.name = 'iteration_statement'
        Node.true = NewLabel()
        Node.false = NewLabel()
        Node.begin = NewLabel()
        if RightExpr[0]['type']=='while':
            Statement = SemanticStack.pop(-1)
            Expression=SemanticStack.pop(-1)
            NewNode.code.append((Node.begin,':','_','_'))
            for code in  Expression.code:
                NewNode.code.append(code)
            NewNode.code.append(('j>',Expression.place,'0',Node.true))
            NewNode.code.append(('j','_','_',Node.false))
            NewNode.code.append((Node.true,':','_','_'))
            for code in Statement.code:
                if code[0]=='break':
                    NewNode.code.append(('j','_','_',Node.false))
                elif code[0]=='continue':
                    NewNode.code.append(('j','_','_',Node.begin))
                else:
                    NewNode.code.append(code)
            NewNode.code.append(('j', '_', '_', Node.begin))
            NewNode.code.append((Node.false,':','_','_'))
        elif RightExpr[0]['type']=='for':
            Statement= SemanticStack.pop(-1)
            Assign= SemanticStack.pop(-1)
            Expression=SemanticStack.pop(-1)
            Declaration=SemanticStack.pop(-1)
            for code in  Declaration.code:
                NewNode.code.append(code)
            NewNode.code.append((Node.begin,':','_','_'))
            for code in  Expression.code:
                NewNode.code.append(code)
            NewNode.code.append(('j>',Expression.place,'0',Node.true))
            NewNode.code.append(('j','_','_',Node.false))
            NewNode.code.append((Node.true,':','_','_'))
            for code in Statement.code:
                if code[0]=='break':
                    NewNode.code.append(('j','_','_',Node.false))
                elif code[0]=='continue':
                    NewNode.code.append(('j','_','_',Node.begin))
                else:
                    NewNode.code.append(code)
            for code in Assign.code:
                NewNode.code.append(code)
            NewNode.code.append(('j', '_', '_', Node.begin))
            NewNode.code.append((Node.false,':','_','_'))
        SemanticStack.append(NewNode)
    elif LeftExpr=='function_declaration':
        NewNode = Node()
        NewNode.name = 'function_declaration'
        name = OpStack[-1]['data']
        NewNode.id = name
        NewNode.type=SemanticStack.pop(-1).type
        NewNode.place=NewTemp()
        SemanticStack.append(NewNode)
    elif LeftExpr=='function_declaration_suffix':
        NewNode = Node()
        NewNode.name = 'function_declaration_suffix'
        if len(RightExpr)==1:
            NewNode.stack=[]
        else:
            NewNode=SemanticStack.pop(-1)
            NewNode.stack.insert(0,SemanticStack.pop(-1))
        SemanticStack.append(NewNode)
    elif LeftExpr == 'function_declaration_list':
        NewNode = Node()
        NewNode.name = 'function_declaration_list'
        if len(RightExpr) == 1:
            NewNode.stack = []
        else:
            NewNode = SemanticStack.pop(-1)
            NewNode.stack.insert(0, SemanticStack.pop(-1))
        SemanticStack.append(NewNode)
    elif LeftExpr == 'function_definition':
        global CurrentFunctionSymbol
        NewNode = SemanticStack.pop(-1)
        NewNode.name = 'function_definition'
        function=FunctionSymbol()
        Type=SemanticStack.pop(-1)
        function.type=Type.type
        function.name=OpStack[-4]['data']
        if function.name=='main':
            function.lable ='main'
        else:
            function.lable=NewFunction()
        for arg in NewNode.stack:
            symbol=Symbol()
            symbol.name=arg.id
            symbol.type=arg.type
            symbol.place=arg.place
            symbol.function = function.lable
            symbol.size=4
            #global CurrentOffset
            symbol.offset=CurrentOffset
            CurrentOffset+=symbol.size
            UpdateSymbolTable(symbol)
            function.params.append((arg.id,arg.type,arg.place))
        NewNode.data=function.lable
        UpdateFunctionTable(function)
        CurrentFunctionSymbol=function
        SemanticStack.append(NewNode)
    elif LeftExpr == 'function_implement':
        NewNode = SemanticStack.pop(-1)
        Definition=SemanticStack.pop(-1)
        NewNode.name = 'function_implement'
        tempcode=[]
        tempcode.append((Definition.data,':','_','_'))
        for node in Definition.stack:
            tempcode.append(('pop','_',4*Definition.stack.index(node),node.place))
        if len(Definition.stack)>0:
            tempcode.append(('-', 'fp', 4*len(Definition.stack), 'fp'))
        tempcode.append(('-', 'sp', 4*len(Definition.stack)+4, 'sp'))
        tempcode.append(('store', '_', 4*len(Definition.stack), 'ra'))
        for node in Definition.stack:
            tempcode.append(('store','_',4*Definition.stack.index(node),node.place))
        for code in reversed(tempcode):
            NewNode.code.insert(0,code)
        end=NewNode.code[-1]
        if end[0][0]=='l':
            lable=end[0]
            NewNode.code.remove(end)
            for code in NewNode.code:
                if code[3]==lable:
                    NewNode.code.remove(code)
        SemanticStack.append(NewNode)
    elif LeftExpr == 'function_expression':
        function = FindFunctionByName(OpStack[-4]['data'])
        NewNode = SemanticStack.pop(-1)
        NewNode.name = 'function_expression'
        if len(function.params)>0:
            NewNode.code.append(('+', 'fp', 4*len(function.params), 'fp'))
        for node in NewNode.stack:
            if node.place!=None:
                result=node.place
            else:
                result = node.data
            NewNode.code.append(('push','_',4*NewNode.stack.index(node),result))
        NewNode.code.append(('call', '_', '_', function.lable))
        NewNode.place=NewTemp()
        NewNode.code.append((':=', 'v0', '_', NewNode.place))
        TempList=copy.deepcopy(function.params)
        TempList.reverse()
        for node in TempList:
            NewNode.code.append(('load', '_', 4*TempList.index(node), node[2]))
        NewNode.code.append(('load', '_', 4*len(TempList), 'ra'))
        SemanticStack.append(NewNode)
    elif LeftExpr =='external_declaration':
        NewNode = SemanticStack.pop(-1)
        NewNode.name = 'external_declaration'
        SemanticStack.append(NewNode)
    elif LeftExpr =='start':
        NewNode = Node()
        NewNode.name = 'start'
        if len(RightExpr)==1:
            NewNode.stack=[]
        else:
            NewNode=SemanticStack.pop(-1)
            NewNode.stack.insert(0,SemanticStack.pop(-1))
            for node in NewNode.stack:
                for code in reversed(node.code):
                    NewNode.code.insert(0,code)
            NewNode.stack=[]
        SemanticStack.append(NewNode)
    return
def PrintIntermediateCode(codes):
    for code in codes:
        if code[0]==':=':
            print('{}={}'.format(code[3],code[1]))
        elif code[1]==':':
            if code[0][0]=='f':
                print('')
            print('{}:'.format(code[0]))
        elif code[0]=='call' or code[0]=='push' or code[0]=='pop'or code[0]=='store' or code[0]=='load' or code[0]=='j':
            print('{}  {}'.format(code[0], code[3]))
        elif code[0]=='j>':
            print('j>0 {} {}'.format(code[1], code[3]))
        elif code[0]=='return':
            print('return')
        else:
            print('{}={}{}{}'.format(code[3], code[1], code[0], code[2]))
CurrentLable=0
CurrentTemp=0
CurrentFunction=0
CurrentStep=0
CurrentOffset=0
CurrentProduction=None
CurrentFunctionSymbol=None
ProductionGroup=[]
DotedProductionGroup=[]
TerminalSymbolGroup=[]
LeftGroup=[]
StateIndexTable={}
TerminalIndexTable={}
NonterminalIndexTable={}
ACTION=[]
GOTO=[]
StartProduction=None
DFA=DFA()
Reduce={}
Shift={}
FIRST={}
FOLLOW={}
OpStack = []
#状态栈
StateStack = []
Table=None
SymbolTable=[]
FunctionTable=[]
#语义栈
SemanticStack=[]
Tokens=[]
Regs={'$'+str(x):'' for x in range(7,26)}
TempValueStatus={}
Mips=[]
StackOffset=8000
DataSegment=10010000
if __name__=='__main__':
    ReadGrammer("grammer.txt")
    GenerateDotedproductions()
    # PrintGrammer(ProductionGroup)
    GenerateFirst()
    GenerateDFA()
    #DrawGraph()
    GenerateTable()
    #PrintTable()
    #global Tokens
    Tokens=main('test1.c')
    #Tokens = main('test.c')
    MakeAnalyse()
    temp=SymbolTable
    codes=SemanticStack[0].code
    PrintIntermediateCode(codes)
    #print('------------------------------')
    #GenerateMips(codes)
    #for code in Mips:
    #    print(code)