from sortedcontainers import SortedSet

def extend(s, var, val):
    """Copy dict s and extend it by setting var to val; return copy."""
    return {**s, var: val}

def first(iterable, default=None):
    """Return the first element of an iterable; or default."""
    return next(iter(iterable), default)

# ______________________________________________________________________________

def sat_up(to_do):
    return SortedSet(to_do, key=lambda t: 1 / len([var for var in t[1].scope]))

def partition_domain(dom):
    """Partitions domain dom into two"""
    split = len(dom) // 2
    dom1 = set(list(dom)[:split])
    dom2 = dom - dom1
    return dom1, dom2

class ACSolver:
    """Solves a CSP with arc consistency and domain splitting"""

    def __init__(self, csp):
        """a CSP solver that uses arc consistency
        * csp is the CSP to be solved
        """
        self.csp = csp

    def GAC(self, orig_domains=None, to_do=None, arc_heuristic=sat_up):
        """
        Makes this CSP arc-consistent using Generalized Arc Consistency
        orig_domains: is the original domains
        to_do       : is a set of (variable,constraint) pairs
        returns the reduced domains (an arc-consistent variable:domain dictionary)
        """
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
                    if const.holds({var: val}):
                        new_domain.add(val)
                    checks += 1
                # new_domain = {val for val in domains[var]
                #               if const.holds({var: val})}
            elif len(other_vars) == 1:
                other = other_vars[0]
                for val in domains[var]:
                    for other_val in domains[other]:
                        checks += 1
                        if const.holds({var: val, other: other_val}):
                            new_domain.add(val)
                            break
                # new_domain = {val for val in domains[var]
                #               if any(const.holds({var: val, other: other_val})
                #                      for other_val in domains[other])}
            else:  # general case
                for val in domains[var]:
                    holds, checks = self.any_holds(domains, const, {var: val}, other_vars, checks=checks)
                    if holds:
                        new_domain.add(val)
                # new_domain = {val for val in domains[var]
                #               if self.any_holds(domains, const, {var: val}, other_vars)}
            if new_domain != domains[var]:
                domains[var] = new_domain
                if not new_domain:
                    return False, domains, checks
                add_to_do = self.new_to_do(var, const).difference(to_do)
                to_do |= add_to_do
        return True, domains, checks

    def new_to_do(self, var, const):
        """
        Returns new elements to be added to to_do after assigning
        variable var in constraint const.
        """
        return {(nvar, nconst) for nconst in self.csp.var_to_const[var]
                if nconst != const
                for nvar in nconst.scope
                if nvar != var}

    def any_holds(self, domains, const, env, other_vars, ind=0, checks=0):
        """
        Returns True if Constraint const holds for an assignment
        that extends env with the variables in other_vars[ind:]
        env is a dictionary
        Warning: this has side effects and changes the elements of env
        """
        if ind == len(other_vars):
            return const.holds(env), checks + 1
        else:
            var = other_vars[ind]
            for val in domains[var]:
                # env = dict_union(env, {var:val})  # no side effects
                env[var] = val
                holds, checks = self.any_holds(domains, const, env, other_vars, ind + 1, checks)
                if holds:
                    return True, checks
            return False, checks

    def domain_splitting(self, domains=None, to_do=None, arc_heuristic=sat_up):
        """
        Return a solution to the current CSP or False if there are no solutions
        to_do is the list of arcs to check
        """
        if domains is None:
            domains = self.csp.domains
        consistency, new_domains, _ = self.GAC(domains, to_do, arc_heuristic)
        if not consistency:
            return False
        elif all(len(new_domains[var]) == 1 for var in domains):
            return {var: first(new_domains[var]) for var in domains}
        else:
            var = first(x for x in self.csp.variables if len(new_domains[x]) > 1)
            if var:
                dom1, dom2 = partition_domain(new_domains[var])
                new_doms1 = extend(new_domains, var, dom1)
                new_doms2 = extend(new_domains, var, dom2)
                to_do = self.new_to_do(var, None)
                return self.domain_splitting(new_doms1, to_do, arc_heuristic) or \
                       self.domain_splitting(new_doms2, to_do, arc_heuristic)

def ac_solver(csp, arc_heuristic=sat_up):
    """Arc consistency (domain splitting interface)"""
    return ACSolver(csp).domain_splitting(arc_heuristic=arc_heuristic)


# ______________________________________________________________________________



class Constraint:
    def __init__(self,scope,condition):
        self.scope = scope
        self.condition = condition

    def __repr__(self):
        return self.condition.__name__ + str(self.scope)

    def holds(self, assignment):
        """Returns the value of Constraint con evaluated in assignment.

        precondition: all variables are assigned in assignment
        """
        return self.condition(*tuple(assignment[v] for v in self.scope))

class CSP:
    def __init__(self,domains,constraints):

        self.variables = set(domains)
        self.domains = domains
        self.constraints = constraints
        self.var_to_const = {var: set() for var in self.variables}
        for con in constraints:
            for var in con.scope:
                self.var_to_const[var].add(con)
        
    def consistent(self, assignment):
        """assignment is a variable:value dictionary
        returns True if all of the constraints that can be evaluated
                        evaluate to True given assignment.
        """
        return all(con.holds(assignment)
                   for con in self.constraints
                   if all(v in assignment for v in con.scope))


def all_diff(*arg):
    return len(arg) == len(set(arg))

def eq(a,b):
    return a==b

#__________________________________________________________________________

# x + y + ...  == z
def const_plus_type1(*arg):
    equa = '+'.join(map(str,arg[:-1]))
    equa += f'=={arg[-1]}'
    return eval(equa)

# x + y + ... == z + 10*c1
def const_plus_type2(*arg):
    equa = '+'.join(map(str,arg[:-2]))
    equa += f'=={arg[-2]}+10*{arg[-1]}'
    return eval(equa)

# x + y + ... + c1 == z
def const_plus_type3(*arg):
    equa = '+'.join(map(str,arg[:-2]))
    equa += f'+{arg[-1]}=={arg[-2]}'
    return eval(equa)

# x + y + ... + c1 == z + c2*10
def const_plus_type4(*arg):
    equa = '+'.join(map(str,arg[:-3]))
    equa += f'+{arg[-2]}=={arg[-3]}+{arg[-1]}*10'
    return eval(equa)

#__________________________________________________________________________

# x - y - ...  == z
def const_minus_type1(*arg):
    equa = '-'.join(map(str,arg[:-1]))
    equa += f'=={arg[-1]}'
    return eval(equa)

# x - y - ... + c1*10 == z
def const_minus_type2(*arg):
    equa = '-'.join(map(str,arg[:-2]))
    equa += f'+{arg[-1]}*10=={arg[-2]}'
    return eval(equa)

# x + y + ... - c1 == z
def const_minus_type3(*arg):
    equa = '-'.join(map(str,arg[:-2]))
    equa += f'-{arg[-1]}=={arg[-2]}'
    return eval(equa)

# x + y + ... - c1 + c2*10 == z
def const_minus_type4(*arg):
    equa = '-'.join(map(str,arg[:-3]))
    equa += f'-{arg[-2]}+{arg[-1]}*10=={arg[-3]}'
    return eval(equa)

#__________________________________________________________________________

def const_multi_type1(x,y,z,c1):
    return eval(f'{x} * {y} == {z} + {c1}*10')

def const_multi_type2(*arg):
    s = '0'
    l = len(arg)
    for i in range(0,l-3,2):
        s += '+' + str(arg[i]) + '*' + str(arg[i+1])
    s += '+' + str(arg[-2])
    s += '==' + str(arg[-3])
    s += '+10*' + str(arg[-1])
    return eval(s)

def const_multi_type3(x,y,z,c1):
    return eval(f'{x} * {y} + {c1} == {z}')

def const_multi_type4(x,y,z,c1,c2):
    return eval(f'{x} * {y} + {c1} == {z} + {c2}*10')

def handle_parentheses(equa):
    while equa.find('(') != -1:
        op = equa.find('(')
        cl = equa.find(')')
        if equa[op-1] == '-':
            equa = equa[:op] + equa[op+1:cl].replace('+','.').replace('-','+').replace('.','-') + equa[cl+1:]
        else:
            equa = equa[:op] + equa[op+1:cl] + equa[cl+1:]
    print(equa)

# F O R T Y + T E N + T E N = S I X T Y
forty_ten_ten_sixty = CSP(
                    {'F': set(range(1, 10)), 'O': set(range(0, 10)), 'R': set(range(0, 10)), 
                     'T': set(range(1, 10)), 'Y': set(range(0, 10)), 'E': set(range(0, 10)),
                     'N': set(range(0, 10)), 'S': set(range(1, 10)), 'I': set(range(0, 10)),
                     'X': set(range(0, 10)),
                     'C1': set(range(0, 3)), 'C2': set(range(0, 3)),
                     'C3': set(range(0, 3)), 'C4': set(range(0, 3))
                    },
                    [Constraint(('F', 'O', 'R', 'T', 'Y', 'E', 'N', 'S', 'I', 'X'), all_diff),
                     Constraint(('Y', 'N', 'N', 'Y', 'C1'), const_plus_type2),
                     Constraint(('T', 'E', 'E', 'T' , 'C1', 'C2'), const_plus_type4),
                     Constraint(('R', 'T', 'T', 'X' , 'C2', 'C3'), const_plus_type4),
                     Constraint(('O', 'C3', 'I', 'C4'), const_plus_type2),
                     Constraint(('F', 'C4', 'S'), const_plus_type1)
                    ],
                )

two_two_four = CSP(
                    {'T': set(range(1, 10)), 'F': set(range(1, 10)), 'W': set(range(0, 10)), 
                     'O': set(range(0, 10)), 'U': set(range(0, 10)), 'R': set(range(0, 10)),
                     'C1': set(range(0, 2)), 'C2': set(range(0, 2)), 'C3': set(range(0, 2))
                    },
                    [Constraint(('T', 'F', 'W', 'O', 'U', 'R'), all_diff),
                     Constraint(('O', 'O', 'R', 'C1'), const_plus_type2),
                     Constraint(('W', 'W', 'U', 'C1', 'C2'), const_plus_type4),
                     Constraint(('T', 'T', 'O', 'C2', 'C3'), const_plus_type2),
                     Constraint(('F', 'C3'), eq)
                    ],
                )

# S E N D + M O R E = M O N E Y
send_more_money = CSP(
                        {'S': set(range(1, 10)), 'M': set(range(1, 10)), 'E': set(range(0, 10)), 
                         'N': set(range(0, 10)), 'D': set(range(0, 10)), 'O': set(range(0, 10)), 
                         'R': set(range(0, 10)), 'Y': set(range(0, 10)), 'C1': set(range(0, 2)), 
                         'C2': set(range(0, 2)), 'C3': set(range(0, 2)), 'C4': set(range(0, 2))
                        },
                        [Constraint(('S', 'E', 'N', 'D', 'M', 'O', 'R', 'Y'), all_diff),
                         Constraint(('D', 'E', 'Y', 'C1'), const_plus_type2),
                         Constraint(('N', 'R', 'E', 'C1', 'C2'), const_plus_type4),
                         Constraint(('E', 'O', 'N', 'C2', 'C3'), const_plus_type4),
                         Constraint(('S', 'M', 'O', 'C3', 'C4'), const_plus_type4),
                         Constraint(('M', 'C4'), eq)
                        ]
                    )

# H I + H I = Y O U
hi_hi_you = CSP(
                    {'H': set(range(1, 10)), 'I': set(range(0, 10)), 'Y': set(range(1, 10)), 
                     'O': set(range(0, 10)), 'U': set(range(0, 10)),
                     'C1': set(range(0, 2)), 'C2': set(range(0, 2))
                    },
                    [Constraint(('H', 'I', 'Y', 'O', 'U',), all_diff),
                     Constraint(('I', 'I', 'U', 'C1'), const_plus_type2),
                     Constraint(('H', 'H', 'O', 'C1', 'C2'), const_plus_type4),
                     Constraint(('Y', 'C2'), eq)
                    ],
                )

# H I * H I = B Y E
hi_hi_bye = CSP(
                    {'H': set(range(1, 10)), 'I': set(range(0, 10)), 'B': set(range(1, 10)), 
                     'Y': set(range(0, 10)), 'E': set(range(0, 10)),
                     'C1': set(range(0, 20)), 'C2': set(range(0, 20))
                    },
                    [Constraint(('H', 'I', 'B', 'Y', 'E',), all_diff),
                     Constraint(('I', 'I', 'E', 'C1'), const_multi_type1),
                     Constraint(('I', 'H', 'H', 'I' , 'Y', 'C1', 'C2'), const_multi_type2),
                     Constraint(('H', 'H', 'B', 'C2'), const_multi_type3)
                    ],
                )

# # W H Y * N U T = O N E P O P
# why_nut_onepop = CSP(
#                     {'W': set(range(0, 10)), 'H': set(range(0, 10)), 'Y': set(range(0, 10)), 
#                      'N': set(range(0, 10)), 'U': set(range(0, 10)), 'T': set(range(0, 10)),
#                      'O': set(range(0, 10)), 'E': set(range(0, 10)), 'P': set(range(0, 10)),
#                      'C1': set(range(0, 30)), 'C2': set(range(0, 30)), 'C3': set(range(0, 30)),
#                      'C4': set(range(0, 30)), 'C5': set(range(0, 30)),
#                     },
#                     [Constraint(('W'),diff_zero),
#                      Constraint(('N'),diff_zero),
#                      Constraint(('O'),diff_zero),
#                      Constraint(('W', 'H', 'Y', 'N', 'U', 'T', 'O', 'E', 'P'), all_diff_constraint),
#                      Constraint(('T', 'Y', 'P', 'C1'), const_multi_type1),
#                      Constraint(('T', 'H', 'U', 'Y', 'O', 'C1', 'C2'), const_multi_type2),
#                      Constraint(('T', 'W', 'U', 'H', 'N', 'Y', 'P', 'C2', 'C3'), const_multi_type2),
#                      Constraint(('U', 'W', 'N', 'H', 'E', 'C3', 'C4'), const_multi_type2),
#                      Constraint(('N', 'W', 'N', 'C4', 'C5'), const_multi_type4),
#                      Constraint(('O', 'C5'), eq)
#                     ],
#                 )

# S A Y * M Y = S T Y L E
say_my_style = CSP(
                    {'S': set(range(1, 10)), 'A': set(range(0, 10)), 'Y': set(range(0, 10)), 
                     'M': set(range(1, 10)), 'T': set(range(0, 10)), 'L': set(range(0, 10)),
                     'E': set(range(0, 10)),
                     'C1': set(range(0, 20)), 'C2': set(range(0, 20)),
                     'C3': set(range(0, 20)), 'C4': set(range(0, 20))
                    },
                    [Constraint(('S', 'A', 'Y', 'M', 'T', 'L', 'E',), all_diff),
                     Constraint(('Y', 'Y', 'E', 'C1'), const_multi_type1),
                     Constraint(('Y', 'A', 'M', 'Y' , 'L', 'C1', 'C2'), const_multi_type2),
                     Constraint(('Y', 'S', 'M', 'A' , 'Y', 'C2', 'C3'), const_multi_type2),
                     Constraint(('M', 'S', 'T', 'C3', 'C4'), const_multi_type4),
                     Constraint(('S', 'C4'), eq)
                    ],
                )

# print(ac_solver(hi_hi_you))
# print(ac_solver(two_two_four))
print(ac_solver(send_more_money))

# print('H I * H I = B Y E')
# print(ac_solver(hi_hi_bye))

# print('W H Y * N U T = O N E P O P')
# print(ac_solver(why_nut_onepop))

# print('S A Y * M Y = S T Y L E')
# print(ac_solver(say_my_style))