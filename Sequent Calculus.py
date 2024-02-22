
# Mahan Madani - Sequent Calculus proof system

import re

log = ''

# Patterns
NEGATION_PATTERN = re.compile('^~.+')               # ~A
FORALL_PATTERN = re.compile('^∀.+')                 # ∀x
EXISTS_PATTERN = re.compile('^∃.+')                 # ∃x
IMPLICATION_PATTERN = re.compile('.+->.+')          # A->B
CONJUNCTION_PATTERN = re.compile('.+\^.+')          # A^B
DISJUNCTION_PATTERN = re.compile('.+v.+')           # AvB
BOT_PATTERN = re.compile('^⊥$')                     # ⊥


# after applying a rule, we may need to remove unnecessary parentheses
def remove_parentheses(string):
    if re.search('^\(.*\)$', string) is not None:
        string = string[1:-1]
    return string


# certain rules require a sequent to be divided into 2 separate ones - R^, Lv, L->
def split_sequent(formula, operator):
    if f'){operator}(' in formula:
        a, b = formula.split(f'){operator}(', maxsplit=1)
        a = a[1:]
        b = b[:-1]
    elif f'){operator}' in formula:
        a, b = formula.split(f'){operator}', maxsplit=1)
        a = a[1:]
    elif f'{operator}(' in formula:
        a, b = formula.split(f'{operator}(', maxsplit=1)
        b = b[:-1]
    else:
        a, b = formula.split(operator, maxsplit=1)

    while a.count('(') > a.count(')'):
        a = a + ')'
    while a.count('(') < a.count(')'):
        a = '(' + a

    while b.count('(') > b.count(')'):
        b = b + ')'
    while b.count('(') < b.count(')'):
        b = '(' + b

    return [a, b]


# check to see if sequent can be proven using the logical axiom
def check_axiom(sequent):
    for g in sequent.gamma:
        for d in sequent.delta:
            if g == d:
                print(f"Proved  {sequent.gamma} => {sequent.delta}"
                      f"  with axiom:  {g}, Γ => Δ, {d}\n")
                return True
    return False


# check all formulas in Δ and apply a rule where applicable
def check_delta(sequent):
    passed = False
    gamma = sequent.gamma
    delta = sequent.delta

    for formula in delta:
        negation = re.search(NEGATION_PATTERN, formula)
        forall = re.search(FORALL_PATTERN, formula)
        exists = re.search(EXISTS_PATTERN, formula)
        conjunction = re.search(CONJUNCTION_PATTERN, formula)
        disjunction = re.search(DISJUNCTION_PATTERN, formula)
        implication = re.search(IMPLICATION_PATTERN, formula)

        if negation is not None:
            negation = re.sub('~', '', negation.string)
            negation = remove_parentheses(negation)
            delta.remove(formula)
            gamma.append(negation)
            print("used R~")
            break
        elif forall is not None:
            forall = re.sub('∀.', '', forall.string)
            forall = remove_parentheses(forall)
            delta.remove(formula)
            delta.append(forall)
            print("used R∀")
            break
        elif exists is not None:
            exists = re.sub('∃.', '', exists.string)
            exists = remove_parentheses(exists)
            delta.remove(formula)
            delta.append(exists)
            print("used R∃")
            break
        elif implication is not None:
            a, b = split_sequent(implication.string, '->')
            delta.remove(formula)
            gamma.append(a)
            delta.append(b)
            print("used R->")
            break
        elif conjunction is not None:
            a, b = split_sequent(conjunction.string, '^')
            print("used R^\n")
            prove(Sequent(gamma.copy(), delta + [a]))
            prove(Sequent(gamma.copy(), delta + [b]))
            passed = True
            break
        elif disjunction is not None:
            a, b = split_sequent(disjunction.string, 'v')
            delta.remove(formula)
            delta.append(a)
            delta.append(b)
            print("used Rv")
            break
    return passed


# check all formulas in Γ and apply a rule where applicable
def check_gamma(sequent):
    passed = False
    gamma = sequent.gamma
    delta = sequent.delta

    for formula in gamma:
        negation = re.search(NEGATION_PATTERN, formula)
        forall = re.search(FORALL_PATTERN, formula)
        exists = re.search(EXISTS_PATTERN, formula)
        conjunction = re.search(CONJUNCTION_PATTERN, formula)
        disjunction = re.search(DISJUNCTION_PATTERN, formula)
        implication = re.search(IMPLICATION_PATTERN, formula)
        bot = re.search(BOT_PATTERN, formula)

        if bot is not None:
            passed = True
            print("used L⊥")
            break
        elif negation is not None:
            negation = re.sub('~', '', negation.string)
            negation = remove_parentheses(negation)
            gamma.remove(formula)
            delta.append(negation)
            print("used L~")
            break
        elif forall is not None:
            forall = re.sub('∀.', '', forall.string)
            forall = remove_parentheses(forall)
            gamma.remove(formula)
            gamma.append(forall)
            print("used L∀")
            break
        elif exists is not None:
            exists = re.sub('∃.', '', exists.string)
            exists = remove_parentheses(exists)
            gamma.remove(formula)
            gamma.append(exists)
            print("used L∃")
            break
        elif implication is not None:
            a, b = split_sequent(implication.string, '->')
            gamma.remove(formula)
            print("used L->\n")
            prove(Sequent(gamma.copy(), delta + [a]))
            prove(Sequent(gamma + [b], delta.copy()))
            passed = True
            break
        elif conjunction is not None:
            a, b = split_sequent(conjunction.string, '^')
            gamma.remove(formula)
            gamma.append(a)
            gamma.append(b)
            print("used L^")
            break
        elif disjunction is not None:
            a, b = split_sequent(disjunction.string, 'v')
            gamma.remove(formula)
            print("used Lv\n")
            prove(Sequent(gamma + [a], delta.copy()))
            prove(Sequent(gamma + [b], delta.copy()))
            passed = True
            break

    return passed


# use the 3 function above to recursively prove a sequent - can also be implemented with a while(True) loop
def prove(sequent):
    sequent.print_log()

    if check_axiom(sequent):
        return

    if check_delta(sequent) or check_axiom(sequent):
        return
    else:
        sequent.print_log()

    if not check_gamma(sequent):
        prove(sequent)


# Sequent class contains the formulas in Γ and Δ as lists.
class Sequent:
    def __init__(self, gamma, delta):
        self.gamma = gamma
        self.delta = delta
        self.log = ""

        if '' in self.gamma:
            self.gamma = []
        if '' in self.delta:
            self.delta = []

        self.gamma.append('Γ')
        self.delta.append('Δ')



    def print_log(self):
        if self.log != f"Proving: {self.gamma} => {self.delta}":
            self.log = f"Proving: {self.gamma} => {self.delta}"
            print(self.log)


# Examples:
# =>(∃x(A->B))->((∀xA)->B)
# =>((∃xA)->B)->(∀x(A->B))
# =>(~(∀xA))->(∃x~A)


def setup():
    print("Please enter your logical expression:")
    sequent_str = input().replace(' ', '')
    gamma_str, delta_str = sequent_str.split('=>')

    gamma = gamma_str.split(',')
    delta = delta_str.split(',')

    sequent = Sequent(gamma, delta)
    prove(sequent)


if __name__ == "__main__":
    setup()
