from ctypes import c_char_p
from sortedcontainers import SortedSet
from multiprocessing import Manager, Process

class Constraint:
    def __init__(self,scope,condition) -> None:
        self.scope = scope
        self.condition = condition
        pass

    def __repr__(self) -> str:
        return self.scope.__name__ + str(self.condition)
        pass

    def check_condition(self,assignment) -> bool:
        return self.condition(*(assignment[a] for a in self.scope))
        pass

class CSP:
    def __init__(self,domain,constraints) -> None:
        self.variables = set(domain)
        self.domains = domain
        self.constraints = constraints
        self.var_to_const = {var: set() for var in self.variables}
        for con in constraints:
            for var in con.scope:
                self.var_to_const[var].add(con)
        pass
    def consistent(self, assignment):
        return all(con.check_condition(assignment)
                   for con in self.constraints
                   if all(v in assignment for v in con.scope))

#__________________________________________________________________________

def all_diff(*arg):
    return len(arg) == len(set(arg))

def eq(x,y):
    return x == y

# x + y + ...  == z
# arg = x, y, ..., z
def const_plus_type1(*arg):
    equa = '+'.join(map(str,arg[:-1]))
    equa += f'=={arg[-1]}'
    return eval(equa)

# x + y + ... == z + 10*c1
# arg = x, y, ..., z, c1
def const_plus_type2(*arg):
    equa = '+'.join(map(str,arg[:-2]))
    equa += f'=={arg[-2]}+10*{arg[-1]}'
    return eval(equa)

# x + y + ... + c1 == z
# arg = x, y, ..., z, c1
def const_plus_type3(*arg):
    equa = '+'.join(map(str,arg[:-2]))
    equa += f'+{arg[-1]}=={arg[-2]}'
    return eval(equa)

# x + y + ... + c1 == z + c2*10
# arg = x, y, ..., z, c1, c2
def const_plus_type4(*arg):
    equa = '+'.join(map(str,arg[:-3]))
    equa += f'+{arg[-2]}=={arg[-3]}+{arg[-1]}*10'
    return eval(equa)

# x + y + ... + cl1*10 == a + b + ... + cr1*10
# args = (x, y,....CL1, x, y,... CR1)
def const_plus_multi_op1(*args):
    pivot = args[-1]-1
    left = '+'.join(map(str,args[:pivot]))
    left += f'-{args[pivot]}*10'
    right = '+'.join(map(str,args[pivot+1:-2]))
    right += f'-{args[-2]}*10'
    return eval(left+'=='+right)

# x + y + ... + cl2*10 + cl1 == a + b + ... + cr1*10 + cr2
# args = (x, y,....CL1, CL2, x, y,... CR1, CR2)
def const_plus_multi_op2(*args):
    pivot = args[-1]-1
    left = '+'.join(map(str,args[:pivot-1]))
    left += f'+{args[pivot-1]}-{args[pivot]}*10'
    right = '+'.join(map(str,args[pivot+1:-3]))
    right += f'+{args[-3]}-{args[-2]}*10'
    return eval(left+'=='+right)

# x + y + ... + cl1 == a + b + ... + cr1
# args = (x, y,....CL1, x, y,... CR1)
def const_plus_multi_op3(*args):
    pivot = args[-1]-1
    left = '+'.join(map(str,args[:pivot+1]))
    right = '+'.join(map(str,args[pivot+1:-1]))
    return eval('('+left+')==('+right + ')')

# x * y + h * k + ... = z
# arg = x, y, ..., z
def const_multi_type1(*arg):
    l = len(arg)
    s = '0'
    for i in range(0,l-1,2):
        s += '+' + str(arg[i]) + '*' + str(arg[i+1])
    s += '==' + str(arg[-1])
    return eval(s)

# x * y + ... = z + c1 * 10
# arg = x, y, ..., z, c1
def const_multi_type2(*arg):
    l = len(arg)
    s = '0'
    for i in range(0,l-2,2):
        s += '+' + str(arg[i]) + '*' + str(arg[i+1])
    s += '==' + str(arg[-2]) + '+10*' + str(arg[-1])
    return eval(s)

# x * y + ... + c1 = z
# arg = x, y, ..., z, c1
def const_multi_type3(*arg):
    l = len(arg)
    s = '0'
    for i in range(0,l-2,2):
        s += '+' + str(arg[i]) + '*' + str(arg[i+1])
    s += '+' + str(arg[-1]) + '==' + str(arg[-2])
    return eval(s)

# x * y + ... + c1 = z + c2 * 10
# arg = x, y, ..., z, c1, c2
def const_multi_type4(*arg):
    l = len(arg)
    s = '0'
    for i in range(0,l-3,2):
        s += '+' + str(arg[i]) + '*' + str(arg[i+1])
    s += '+' + str(arg[-2]) + '==' + str(arg[-3]) + '+10*' + str(arg[-1])
    return eval(s)


#__________________________________________________________________________

# convert : a + ( b + c ) = a + b + c 
#      or : a - ( b + c - d ) = a - b - c + d
def handle_parentheses(equa):
    while equa.find('(') != -1:
        op = equa.find('(')
        cl = equa.find(')')
        if equa[op-1] == '-':
            equa = equa[:op] + equa[op+1:cl].replace('+','.').replace('-','+').replace('.','-') + equa[cl+1:]
        else:
            equa = equa[:op] + equa[op+1:cl] + equa[cl+1:]
    return equa

# equa: a + b - c +... = x
# convert: a + b +... = x + c +...
def handle_minus(equa):
    left=''
    right= equa.split('=')[1]
    l = len(equa)
    i = j = 0
    while True:
        if equa[i] == '=':
            break
        elif equa[i] == '-':
            j = i + 1
            while True:
                if equa[j] == '+' or equa[j] == '=':
                    break
                j += 1
            right += equa[i:j].replace('-','+')
            i = j-1
        else:
            left+=equa[i]
        i += 1
    return left + '=' +right

#__________________________________________________________________________
def type_one(left, right, chars_set):
    constraint = []
    domain = {}
    max_len_R = len(right)
    max_len_L = max([len(x) for x in left])
    min_len_L = min([len(x) for x in left])

    for i in range(0,max_len_R-1):
        chars_set.add(f'C{i}')

    for c in chars_set:
        if len(c) > 1:
            domain[c] = set(range(0,len(left)))
        else:
            domain[c] = set(range(0,10))

    if max_len_R > max_len_L:
        domain[right[0]] = set(range(1,len(left)))
    elif max_len_L > max_len_R:
        return
    else:
        domain[right[0]].remove(0)

    right = right[::-1]
    for i in left:
        try:
            domain[i[0]].remove(0)
        except Exception as e:
            pass
    left = [ i[::-1] for i in left]


    constraint.append(Constraint(tuple([k for k in domain.keys() if len(k) == 1]),all_diff))

    for i in range(0,max_len_R):
        scope = []
        scope = [var[i] for var in left if len(var) > i]
        scope.append(right[i])
        if i == 0:
            scope.append(f'C{i}')
            constraint.append(Constraint(tuple(scope),const_plus_type2))
        elif i == max_len_R-1 :
            scope.append(f'C{i-1}')
            constraint.append(Constraint(tuple(scope),const_plus_type3))
        elif i < min_len_L or (min_len_L <= i and i < max_len_L-1):
            scope.append(f'C{i-1}')
            scope.append(f'C{i}')
            constraint.append(Constraint(tuple(scope),const_plus_type4))
        elif max_len_L <= i:
            scope.append(f'C{i-1}')
            constraint.append(Constraint(tuple(scope),eq))
    return domain,constraint
    pass

def type_two(left, right, chars_set):
    constraint = []
    domain = {}
    max_len_R = max([len(x) for x in right])
    min_len_R = min([len(x) for x in right])
    max_len_L = max([len(x) for x in left])
    min_len_L = min([len(x) for x in left])

    max_len = max(max_len_R,max_len_L)

    for i in range(0,max_len):
        chars_set.add(f'CL{i}')
        chars_set.add(f'CR{i}')
        chars_set.add(f'P{i}')

    for c in chars_set:
        if len(c) > 1:
            domain[c] = set(range(0,max(len(left),len(right))))
        else:
            domain[c] = set(range(0,10))

    for i in left:
        try:
            domain[i[0]].remove(0)
        except Exception as e:
            pass
    for i in right:
        try:
            domain[i[0]].remove(0)
        except Exception as e:
            pass

    left = [ i[::-1] for i in left]
    right = [ i[::-1] for i in right]

    constraint.append(Constraint(tuple([k for k in domain.keys() if len(k) == 1]),all_diff))
    for i in range(0,max_len):
        scope = []
        scope = [var[i] for var in left if len(var) > i]
        if i == 0:
            scope.append(f'CL{i}')
            domain[f'P{i}'] = {(len(scope))}
            scope.extend([var[i] for var in right if len(var) > i])
            scope.append(f'CR{i}')
            scope.append(f'P{i}')
            constraint.append(Constraint(scope,const_plus_multi_op1))
        elif i<max_len-1:
            scope.append(f'CL{i-1}')
            scope.append(f'CL{i}')
            domain[f'P{i}'] = {(len(scope))}
            scope.extend([var[i] for var in right if len(var) > i])
            scope.append(f'CR{i-1}')
            scope.append(f'CR{i}')
            scope.append(f'P{i}')
            constraint.append(Constraint(scope, const_plus_multi_op2))
        else:
            scope.append(f'CL{i-1}')
            domain[f'P{i}'] = {(len(scope))}
            scope.extend([var[i] for var in right if len(var) > i])
            scope.append(f'CR{i-1}')
            scope.append(f'P{i}')
            constraint.append(Constraint(scope, const_plus_multi_op3))
    return domain,constraint
    pass

def type_three(left,right,chars_set):
    constraint = []
    domain = {}
    max_len_R = len(right)
    max_len_L = max([len(x) for x in left])
    min_len_L = min([len(x) for x in left])

    if max_len_R < min_len_L + max_len_L - 2:
        return

    for i in range(0,max_len_R-1):
        chars_set.add(f'C{i}')

    for c in chars_set:
        if len(c) > 1:
            domain[c] = set(range(0,min_len_L*10))
        else:
            domain[c] = set(range(0,10))

    domain[right[0]].remove(0)

    right = right[::-1]
    for i in left:
        try:
            domain[i[0]].remove(0)
        except Exception as e:
            pass
    left = [ i[::-1] for i in left]


    constraint.append(Constraint(tuple([k for k in domain.keys() if len(k) == 1]),all_diff))

    count = 1
    for i in range(0,max_len_R):
        scope = []
        for h in range(0,len(left[0])):
            for k in range(0, count):
                if h+k == i:
                    scope.append(left[0][h])
                    scope.append(left[1][k])
        if count < len(left[1]):
            count += 1
        scope.append(right[i])
        if i == 0:
            scope.append(f'C{i}')
            constraint.append(Constraint(tuple(scope),const_multi_type2))
        elif i == max_len_R-1 :
            scope.append(f'C{i-1}')
            constraint.append(Constraint(tuple(scope),const_multi_type3))
        else:
            scope.append(f'C{i-1}')
            scope.append(f'C{i}')
            constraint.append(Constraint(tuple(scope),const_multi_type4))
    return domain,constraint
    pass
       
def handle_input(input_data):
    chars_set = set([e for e in input_data if e.isalpha()])

    domain = None
    constraint = None
    if len(chars_set) <= 10:
        right = None
        left = None        
        if input_data.find('*') != -1:
            right = input_data.split('=')[1]
            left = input_data.split('=')[0].split('*')
            domain, constraint = type_three(left,right,chars_set)
        elif input_data.find('(') != -1:
            equa = handle_parentheses(input_data)
            if equa.find('-') != -1:
                equa = handle_minus(equa)
                right = equa.split('=')[1].split('+')
                left = equa.split('=')[0].split('+')
                domain, constraint = type_two(left,right,chars_set)
            else:
                right = equa.split('=')[1]
                left = equa.split('=')[0].split('+')
                domain, constraint = type_one(left,right,chars_set)
        elif input_data.find('-') != -1:
            equa = handle_minus(input_data)
            left = equa.split('=')[1].split('+')
            right = equa.split('=')[0]
            domain, constraint = type_one(left,right,chars_set)
        else:
            left = input_data.split('=')[0].split('+')
            right = input_data.split('=')[1]
            domain, constraint = type_one(left,right,chars_set)   
    else:
        print("Invalid strings")
        return

    if domain != None and constraint != None:
        return CSP(domain,constraint)
    return

#__________________________________________________________________________

def extend(s, var, val):
    return {**s, var: val}

def first(iterable, default=None):
    return next(iter(iterable), default)

def LCV(to_do):
    return SortedSet(to_do, key=lambda t: 1 / len([var for var in t[1].scope]))

def partition_domain(dom):
    split = len(dom) // 2
    dom1 = set(list(dom)[:split])
    dom2 = dom - dom1
    return dom1, dom2

class ACSolver:
    def __init__(self, csp):
        self.csp = csp

    def gen_ac(self, orig_domains=None, to_do=None, arc_heuristic=LCV):
        if orig_domains is None:
            orig_domains = self.csp.domains
        if to_do is None:
            to_do = {(var, const) for const in self.csp.constraints for var in const.scope}
        else:
            to_do = to_do.copy()
        domains = orig_domains.copy()
        to_do = arc_heuristic(to_do)
        checks = 0
        while to_do:
            var, const = to_do.pop()
            other_vars = [ov for ov in const.scope if ov != var]
            new_domain = set()
            if len(other_vars) == 0:
                for val in domains[var]:
                    if const.check_condition({var: val}):
                        new_domain.add(val)
                    checks += 1
            elif len(other_vars) == 1:
                other = other_vars[0]
                for val in domains[var]:
                    for other_val in domains[other]:
                        checks += 1
                        if const.check_condition({var: val, other: other_val}):
                            new_domain.add(val)
                            break
            else: 
                for val in domains[var]:
                    holds, checks = self.back_track(domains, const, {var: val}, other_vars, checks=checks)
                    if holds:
                        new_domain.add(val)
            if new_domain != domains[var]:
                domains[var] = new_domain
                if not new_domain:
                    return False, domains, checks
                add_to_do = self.new_to_do(var, const).difference(to_do)
                to_do |= add_to_do
        return True, domains, checks

    def new_to_do(self, var, const):
        return {(v, c) for c in self.csp.var_to_const[var]
                if c != const
                for v in c.scope
                if v != var}

    def back_track(self, domains, const, env, other, i=0, checks=0):
        if i == len(other):
            return const.check_condition(env), checks + 1
        else:
            var = other[i]
            for val in domains[var]:
                env[var] = val
                holds, checks = self.back_track(domains, const, env, other, i + 1, checks)
                if holds:
                    return True, checks
            return False, checks

    def domain_splitting(self, domains=None, to_do=None, arc_heuristic=LCV):
        if domains is None:
            domains = self.csp.domains
        consistency, new_domain, _ = self.gen_ac(domains, to_do, arc_heuristic)
        if not consistency:
            return False
        elif all(len(new_domain[var]) == 1 for var in domains):
            return {var: first(new_domain[var]) for var in domains}
        else:
            var = first(x for x in self.csp.variables if len(new_domain[x]) > 1)
            if var:
                dom1, dom2 = partition_domain(new_domain[var])
                new_dom1 = extend(new_domain, var, dom1)
                new_dom2 = extend(new_domain, var, dom2)
                to_do = self.new_to_do(var, None)
                return self.domain_splitting(new_dom1, to_do, arc_heuristic) or \
                       self.domain_splitting(new_dom2, to_do, arc_heuristic)

def ac_solver(csp,solution = None, arc_heuristic=LCV):
    sol =  ACSolver(csp).domain_splitting(arc_heuristic=arc_heuristic)
    if sol:
        l = r = ""
        for k in sorted(sol.keys()):
            if len(k) == 1:
                l+=str(k)
                r+=str(sol[k])
        if solution:
            solution.value = l + '=' + r
        else:
            return l+'='+r
        

#__________________________________________________________________________

def main(waiting_time):
    leve_l = []
    leve_l.append('YOUR+YOU=HEART')
    leve_l.append('BASE+BALL=GAMES')
    leve_l.append('FOUR+ONE=FIVE')
    leve_l.append('QUADRA-DOUBLE=DOUBLE')
    leve_l.append('INTERNET-NETWORK=MONITOR')

    for inp in leve_l:
        csp = handle_input(inp)
        if csp:
            print(f"Maximum time is: {waiting_time}s")
            print(inp)
            manager = Manager()
            solution = manager.Value(c_char_p,'NO SOLUTION')
            p = Process(target=ac_solver, name="Solver", args=(csp,solution,))
            p.start()
            p.join(timeout=waiting_time)
            p.terminate()
            print(solution.value)
            print("Done")
        else:
            print("Invalid strings")

if __name__ == "__main__":
    waiting_time = 350
    main(waiting_time)
