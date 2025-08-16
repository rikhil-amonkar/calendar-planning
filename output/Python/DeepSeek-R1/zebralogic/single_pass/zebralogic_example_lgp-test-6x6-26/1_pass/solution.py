import json
from copy import deepcopy

def main():
    attributes = ['name', 'phone', 'cigar', 'flower', 'color', 'sport']
    initial_domains = {
        'name': ['Peter', 'Carol', 'Eric', 'Alice', 'Bob', 'Arnold'],
        'phone': ['huawei p50', 'google pixel 6', 'xiaomi mi 11', 'iphone 13', 'samsung galaxy s21', 'oneplus 9'],
        'cigar': ['dunhill', 'pall mall', 'blends', 'blue master', 'prince', 'yellow monster'],
        'flower': ['daffodils', 'carnations', 'roses', 'tulips', 'lilies', 'iris'],
        'color': ['yellow', 'red', 'green', 'blue', 'white', 'purple'],
        'sport': ['soccer', 'tennis', 'basketball', 'volleyball', 'swimming', 'baseball']
    }
    
    domains = {}
    for attr in attributes:
        for i in range(6):
            domains[(attr, i)] = set(initial_domains[attr])
    
    domains[('phone', 1)] = {'oneplus 9'}
    domains[('name', 0)] = {'Alice'}

    def constraint1(assignment):
        if assignment['phone'][1] is not None:
            return assignment['phone'][1] == 'oneplus 9'
        return True

    def constraint2(assignment):
        if 'xiaomi mi 11' in assignment['phone'] and 'huawei p50' in assignment['phone']:
            i = assignment['phone'].index('xiaomi mi 11')
            j = assignment['phone'].index('huawei p50')
            return i < j
        return True

    def constraint3(assignment):
        for i in range(6):
            if assignment['name'][i] == 'Carol' and assignment['flower'][i] is not None:
                if assignment['flower'][i] != 'carnations':
                    return False
            if assignment['flower'][i] == 'carnations' and assignment['name'][i] is not None:
                if assignment['name'][i] != 'Carol':
                    return False
        return True

    def constraint4(assignment):
        if 'purple' in assignment['color'] and 'pall mall' in assignment['cigar']:
            i = assignment['color'].index('purple')
            j = assignment['cigar'].index('pall mall')
            return j == i + 1
        return True

    def constraint5(assignment):
        if 'green' in assignment['color'] and 'blue master' in assignment['cigar']:
            i = assignment['color'].index('green')
            j = assignment['cigar'].index('blue master')
            return i == j
        return True

    def constraint6(assignment):
        if 'yellow' in assignment['color'] and 'blue' in assignment['color']:
            i = assignment['color'].index('yellow')
            j = assignment['color'].index('blue')
            return abs(i - j) == 1
        return True

    def constraint7(assignment):
        if 'samsung galaxy s21' in assignment['phone'] and 'Eric' in assignment['name']:
            i = assignment['phone'].index('samsung galaxy s21')
            j = assignment['name'].index('Eric')
            return i < j
        return True

    def constraint8(assignment):
        if 'Carol' in assignment['name'] and 'daffodils' in assignment['flower']:
            i = assignment['name'].index('Carol')
            j = assignment['flower'].index('daffodils')
            return abs(i - j) == 3
        return True

    def constraint9(assignment):
        if 'prince' in assignment['cigar'] and 'basketball' in assignment['sport']:
            i = assignment['cigar'].index('prince')
            j = assignment['sport'].index('basketball')
            return i == j
        return True

    def constraint10(assignment):
        if 'dunhill' in assignment['cigar'] and 'volleyball' in assignment['sport']:
            i = assignment['cigar'].index('dunhill')
            j = assignment['sport'].index('volleyball')
            return i == j
        return True

    def constraint11(assignment):
        if 'swimming' in assignment['sport'] and 'google pixel 6' in assignment['phone']:
            i = assignment['sport'].index('swimming')
            j = assignment['phone'].index('google pixel 6')
            return i == j
        return True

    def constraint12(assignment):
        if 'huawei p50' in assignment['phone'] and 'white' in assignment['color']:
            i = assignment['phone'].index('huawei p50')
            j = assignment['color'].index('white')
            return j == i + 1
        return True

    def constraint13(assignment):
        if 'oneplus 9' in assignment['phone'] and 'roses' in assignment['flower']:
            i = assignment['phone'].index('oneplus 9')
            j = assignment['flower'].index('roses')
            return abs(i - j) == 1
        return True

    def constraint14(assignment):
        if 'iris' in assignment['flower'] and 'Eric' in assignment['name']:
            i = assignment['flower'].index('iris')
            j = assignment['name'].index('Eric')
            return i < j
        return True

    def constraint15(assignment):
        for i in range(6):
            if assignment['cigar'][i] == 'dunhill' and assignment['name'][i] is not None:
                if assignment['name'][i] != 'Peter':
                    return False
            if assignment['name'][i] == 'Peter' and assignment['cigar'][i] is not None:
                if assignment['cigar'][i] != 'dunhill':
                    return False
        return True

    def constraint16(assignment):
        for i in range(6):
            if assignment['color'][i] == 'blue' and assignment['name'][i] is not None:
                if assignment['name'][i] != 'Peter':
                    return False
            if assignment['name'][i] == 'Peter' and assignment['color'][i] is not None:
                if assignment['color'][i] != 'blue':
                    return False
        return True

    def constraint17(assignment):
        for i in range(6):
            if assignment['flower'][i] == 'tulips' and assignment['name'][i] is not None:
                if assignment['name'][i] != 'Bob':
                    return False
            if assignment['name'][i] == 'Bob' and assignment['flower'][i] is not None:
                if assignment['flower'][i] != 'tulips':
                    return False
        return True

    def constraint18(assignment):
        if assignment['name'][0] is not None:
            return assignment['name'][0] == 'Alice'
        return True

    def constraint19(assignment):
        if 'baseball' in assignment['sport'] and 'blue master' in assignment['cigar']:
            i = assignment['sport'].index('baseball')
            j = assignment['cigar'].index('blue master')
            return j == i + 1
        return True

    def constraint20(assignment):
        if 'blends' in assignment['cigar'] and 'google pixel 6' in assignment['phone']:
            i = assignment['cigar'].index('blends')
            j = assignment['phone'].index('google pixel 6')
            return i < j
        return True

    def constraint21(assignment):
        for i in range(6):
            if assignment['sport'][i] == 'soccer' and assignment['name'][i] is not None:
                if assignment['name'][i] != 'Carol':
                    return False
            if assignment['name'][i] == 'Carol' and assignment['sport'][i] is not None:
                if assignment['sport'][i] != 'soccer':
                    return False
        return True

    def constraint22(assignment):
        if 'carnations' in assignment['flower'] and 'blends' in assignment['cigar']:
            i = assignment['flower'].index('carnations')
            j = assignment['cigar'].index('blends')
            return j == i + 1
        return True

    def constraint23(assignment):
        for i in range(6):
            if assignment['cigar'][i] == 'blends' and assignment['name'][i] is not None:
                if assignment['name'][i] != 'Eric':
                    return False
            if assignment['name'][i] == 'Eric' and assignment['cigar'][i] is not None:
                if assignment['cigar'][i] != 'blends':
                    return False
        return True

    def constraint24(assignment):
        if 'volleyball' in assignment['sport'] and 'iphone 13' in assignment['phone']:
            i = assignment['sport'].index('volleyball')
            j = assignment['phone'].index('iphone 13')
            return i == j
        return True

    def constraint_peter(assignment):
        for i in range(6):
            if assignment['name'][i] == 'Peter':
                if assignment['cigar'][i] is not None and assignment['cigar'][i] != 'dunhill':
                    return False
                if assignment['color'][i] is not None and assignment['color'][i] != 'blue':
                    return False
                if assignment['sport'][i] is not None and assignment['sport'][i] != 'volleyball':
                    return False
                if assignment['phone'][i] is not None and assignment['phone'][i] != 'iphone 13':
                    return False
        return True

    constraints = [
        constraint1, constraint2, constraint3, constraint4, constraint5,
        constraint6, constraint7, constraint8, constraint9, constraint10,
        constraint11, constraint12, constraint13, constraint14, constraint15,
        constraint16, constraint17, constraint18, constraint19, constraint20,
        constraint21, constraint22, constraint23, constraint24, constraint_peter
    ]

    def check_constraints(assignment):
        for c in constraints:
            if not c(assignment):
                return False
        return True

    def is_complete(assignment):
        for attr in attributes:
            for i in range(6):
                if assignment[attr][i] is None:
                    return False
        return True

    def reduce_domains(old_domains, cell, value):
        new_domains = deepcopy(old_domains)
        attr, i = cell
        for j in range(6):
            if j != i:
                key = (attr, j)
                if value in new_domains[key]:
                    new_domains[key].remove(value)
                    if len(new_domains[key]) == 0:
                        return None
        return new_domains

    def select_unassigned_variable(assignment, domains):
        min_domain_size = float('inf')
        selected_cell = None
        for attr in attributes:
            for i in range(6):
                if assignment[attr][i] is None:
                    key = (attr, i)
                    domain_size = len(domains[key])
                    if domain_size < min_domain_size:
                        min_domain_size = domain_size
                        selected_cell = key
        return selected_cell

    def backtrack(assignment, domains, constraints):
        if is_complete(assignment):
            if check_constraints(assignment):
                return assignment
            return None

        cell = select_unassigned_variable(assignment, domains)
        if cell is None:
            return None

        attr, i = cell
        for value in list(domains[cell]):
            assignment[attr][i] = value
            new_domains = reduce_domains(domains, cell, value)
            if new_domains is None:
                assignment[attr][i] = None
                continue
            if check_constraints(assignment):
                result = backtrack(assignment, new_domains, constraints)
                if result is not None:
                    return result
            assignment[attr][i] = None

        return None

    initial_assignment = {
        'name': [None] * 6,
        'phone': [None] * 6,
        'cigar': [None] * 6,
        'flower': [None] * 6,
        'color': [None] * 6,
        'sport': [None] * 6
    }
    initial_assignment['name'][0] = 'Alice'
    initial_assignment['phone'][1] = 'oneplus 9'

    solution = backtrack(initial_assignment, domains, constraints)
    if solution is None:
        print('No solution found')
    else:
        output = {
            "solution": {
                "header": ["House", "Name", "PhoneModel", "Cigar", "Flower", "Color", "FavoriteSport"],
                "rows": []
            }
        }
        for i in range(6):
            row = [
                str(i+1),
                solution['name'][i],
                solution['phone'][i],
                solution['cigar'][i],
                solution['flower'][i],
                solution['color'][i],
                solution['sport'][i]
            ]
            output['solution']['rows'].append(row)
        print(json.dumps(output))

if __name__ == '__main__':
    main()