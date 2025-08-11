import copy
import json

def main():
    attributes = ['name', 'phone', 'cigar', 'flower', 'color', 'sport']
    attr_index = {attr: idx for idx, attr in enumerate(attributes)}
    
    values = {
        'name': ['Peter', 'Carol', 'Eric', 'Alice', 'Bob', 'Arnold'],
        'phone': ['huawei p50', 'google pixel 6', 'xiaomi mi 11', 'iphone 13', 'samsung galaxy s21', 'oneplus 9'],
        'cigar': ['dunhill', 'pall mall', 'blends', 'blue master', 'prince', 'yellow monster'],
        'flower': ['daffodils', 'carnations', 'roses', 'tulips', 'lilies', 'iris'],
        'color': ['yellow', 'red', 'green', 'blue', 'white', 'purple'],
        'sport': ['soccer', 'tennis', 'basketball', 'volleyball', 'swimming', 'baseball']
    }
    
    n = 6
    domains = [[set(values[attr]) for attr in attributes] for _ in range(n)]
    
    domains[1][attr_index['phone']] = {'oneplus 9'}
    domains[0][attr_index['name']] = {'Alice'}
    
    def propagate_uniqueness(domains):
        changed = False
        n_houses = len(domains)
        n_attrs = len(domains[0])
        for a in range(n_attrs):
            fixed_values = {}
            for i in range(n_houses):
                if len(domains[i][a]) == 1:
                    val = next(iter(domains[i][a]))
                    if val not in fixed_values:
                        fixed_values[val] = []
                    fixed_values[val].append(i)
            for val, houses in fixed_values.items():
                if len(houses) > 1:
                    continue
                for i in range(n_houses):
                    if i not in houses and val in domains[i][a]:
                        domains[i][a].discard(val)
                        changed = True
        return changed

    def propagate_same_house(domains, attr1, value1, attr2, value2):
        changed = False
        n_houses = len(domains)
        A = set()
        B = set()
        for i in range(n_houses):
            if value1 in domains[i][attr1]:
                A.add(i)
            if value2 in domains[i][attr2]:
                B.add(i)
        common = A & B
        for i in (A - common):
            if value1 in domains[i][attr1]:
                domains[i][attr1].discard(value1)
                changed = True
        for i in (B - common):
            if value2 in domains[i][attr2]:
                domains[i][attr2].discard(value2)
                changed = True
        return changed

    def propagate_left_neighbor(domains, attr1, value1, attr2, value2):
        changed = False
        n_houses = len(domains)
        possible_i = []
        for i in range(0, n_houses-1):
            if value1 in domains[i][attr1] and value2 in domains[i+1][attr2]:
                possible_i.append(i)
        for i in range(0, n_houses-1):
            if value1 in domains[i][attr1] and i not in possible_i:
                domains[i][attr1].discard(value1)
                changed = True
        for i in range(1, n_houses):
            if value2 in domains[i][attr2] and (i-1) not in possible_i:
                domains[i][attr2].discard(value2)
                changed = True
        if value1 in domains[n_houses-1][attr1]:
            domains[n_houses-1][attr1].discard(value1)
            changed = True
        if value2 in domains[0][attr2]:
            domains[0][attr2].discard(value2)
            changed = True
        return changed

    def propagate_adjacent(domains, attr1, value1, attr2, value2):
        changed = False
        n_houses = len(domains)
        A = set()
        for i in range(n_houses):
            if value1 in domains[i][attr1]:
                A.add(i)
        B = set()
        for i in range(n_houses):
            if value2 in domains[i][attr2]:
                B.add(i)
        for i in A:
            if not ((i-1 in B) or (i+1 in B)):
                domains[i][attr1].discard(value1)
                changed = True
        for j in B:
            if not ((j-1 in A) or (j+1 in A)):
                domains[j][attr2].discard(value2)
                changed = True
        return changed

    def propagate_left_of(domains, attr1, value1, attr2, value2):
        changed = False
        n_houses = len(domains)
        A = set()
        for i in range(n_houses):
            if value1 in domains[i][attr1]:
                A.add(i)
        B = set()
        for i in range(n_houses):
            if value2 in domains[i][attr2]:
                B.add(i)
        new_A = set()
        for i in A:
            if any(j > i for j in B):
                new_A.add(i)
        for i in A - new_A:
            domains[i][attr1].discard(value1)
            changed = True
        new_B = set()
        for j in B:
            if any(i < j for i in A):
                new_B.add(j)
        for j in B - new_B:
            domains[j][attr2].discard(value2)
            changed = True
        return changed

    constraints = []
    
    def c2(domains):
        return propagate_left_of(domains, attr_index['phone'], 'xiaomi mi 11', attr_index['phone'], 'huawei p50')
    constraints.append(c2)
    
    def c3(domains):
        return propagate_same_house(domains, attr_index['name'], 'Carol', attr_index['flower'], 'carnations')
    constraints.append(c3)
    
    def c4(domains):
        return propagate_left_neighbor(domains, attr_index['color'], 'purple', attr_index['cigar'], 'pall mall')
    constraints.append(c4)
    
    def c5(domains):
        return propagate_same_house(domains, attr_index['color'], 'green', attr_index['cigar'], 'blue master')
    constraints.append(c5)
    
    def c6(domains):
        return propagate_adjacent(domains, attr_index['color'], 'yellow', attr_index['color'], 'blue')
    constraints.append(c6)
    
    def c7(domains):
        return propagate_left_of(domains, attr_index['phone'], 'samsung galaxy s21', attr_index['name'], 'Eric')
    constraints.append(c7)
    
    def c8(domains):
        changed = False
        a_name = attr_index['name']
        a_flower = attr_index['flower']
        for i in range(n):
            if 'Carol' in domains[i][a_name]:
                if (i+3 < n and 'daffodils' in domains[i+3][a_flower]) or (i-3 >= 0 and 'daffodils' in domains[i-3][a_flower]):
                    pass
                else:
                    domains[i][a_name].discard('Carol')
                    changed = True
        for j in range(n):
            if 'daffodils' in domains[j][a_flower]:
                if (j+3 < n and 'Carol' in domains[j+3][a_name]) or (j-3 >= 0 and 'Carol' in domains[j-3][a_name]):
                    pass
                else:
                    domains[j][a_flower].discard('daffodils')
                    changed = True
        return changed
    constraints.append(c8)
    
    def c9(domains):
        return propagate_same_house(domains, attr_index['cigar'], 'prince', attr_index['sport'], 'basketball')
    constraints.append(c9)
    
    def c10(domains):
        return propagate_same_house(domains, attr_index['cigar'], 'dunhill', attr_index['sport'], 'volleyball')
    constraints.append(c10)
    
    def c11(domains):
        return propagate_same_house(domains, attr_index['sport'], 'swimming', attr_index['phone'], 'google pixel 6')
    constraints.append(c11)
    
    def c12(domains):
        return propagate_left_neighbor(domains, attr_index['phone'], 'huawei p50', attr_index['color'], 'white')
    constraints.append(c12)
    
    def c13(domains):
        return propagate_adjacent(domains, attr_index['phone'], 'oneplus 9', attr_index['flower'], 'roses')
    constraints.append(c13)
    
    def c14(domains):
        return propagate_left_of(domains, attr_index['flower'], 'iris', attr_index['name'], 'Eric')
    constraints.append(c14)
    
    def c15(domains):
        return propagate_same_house(domains, attr_index['name'], 'Peter', attr_index['cigar'], 'dunhill')
    constraints.append(c15)
    
    def c16(domains):
        return propagate_same_house(domains, attr_index['name'], 'Peter', attr_index['color'], 'blue')
    constraints.append(c16)
    
    def c17(domains):
        return propagate_same_house(domains, attr_index['name'], 'Bob', attr_index['flower'], 'tulips')
    constraints.append(c17)
    
    def c19(domains):
        return propagate_left_neighbor(domains, attr_index['sport'], 'baseball', attr_index['cigar'], 'blue master')
    constraints.append(c19)
    
    def c20(domains):
        return propagate_left_of(domains, attr_index['cigar'], 'blends', attr_index['phone'], 'google pixel 6')
    constraints.append(c20)
    
    def c21(domains):
        return propagate_same_house(domains, attr_index['name'], 'Carol', attr_index['sport'], 'soccer')
    constraints.append(c21)
    
    def c22(domains):
        return propagate_left_neighbor(domains, attr_index['flower'], 'carnations', attr_index['cigar'], 'blends')
    constraints.append(c22)
    
    def c23(domains):
        return propagate_same_house(domains, attr_index['name'], 'Eric', attr_index['cigar'], 'blends')
    constraints.append(c23)
    
    def c24(domains):
        return propagate_same_house(domains, attr_index['sport'], 'volleyball', attr_index['phone'], 'iphone 13')
    constraints.append(c24)
    
    def backtrack(domains):
        changed = True
        while changed:
            changed = False
            changed = propagate_uniqueness(domains) or changed
            for constraint in constraints:
                changed = constraint(domains) or changed
                
        for i in range(n):
            for a in range(len(attributes)):
                if len(domains[i][a]) == 0:
                    return None
                    
        all_singleton = True
        for i in range(n):
            for a in range(len(attributes)):
                if len(domains[i][a]) != 1:
                    all_singleton = False
                    break
            if not all_singleton:
                break
                
        if all_singleton:
            sol_rows = []
            for i in range(n):
                row = [str(i+1)]
                for a in range(len(attributes)):
                    row.append(next(iter(domains[i][a])))
                sol_rows.append(row)
            return sol_rows
            
        min_domain_size = 100
        min_i = -1
        min_a = -1
        for i in range(n):
            for a in range(len(attributes)):
                domain_size = len(domains[i][a])
                if domain_size > 1 and domain_size < min_domain_size:
                    min_domain_size = domain_size
                    min_i = i
                    min_a = a
                    
        if min_i == -1:
            return None
            
        for val in domains[min_i][min_a]:
            new_domains = copy.deepcopy(domains)
            new_domains[min_i][min_a] = {val}
            res = backtrack(new_domains)
            if res is not None:
                return res
                
        return None
        
    solution = backtrack(domains)
    
    if solution is None:
        print('{"solution": {}}')
    else:
        output = {
            "solution": {
                "header": ["House"] + attributes,
                "rows": solution
            }
        }
        print(json.dumps(output))

if __name__ == "__main__":
    main()