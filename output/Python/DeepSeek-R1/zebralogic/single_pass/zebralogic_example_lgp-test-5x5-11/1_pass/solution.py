import copy
import json

def main():
    attributes_list = {
        'Name': ['Peter', 'Arnold', 'Eric', 'Bob', 'Alice'],
        'Height': ['average', 'very tall', 'very short', 'short', 'tall'],
        'Cigar': ['prince', 'dunhill', 'blends', 'pall mall', 'blue master'],
        'Smoothie': ['lime', 'cherry', 'dragonfruit', 'watermelon', 'desert'],
        'Phone': ['oneplus 9', 'samsung galaxy s21', 'iphone 13', 'huawei p50', 'google pixel 6']
    }
    
    def c1(assignment):
        prince_house = None
        desert_house = None
        for i, house in enumerate(assignment):
            if 'Cigar' in house and house['Cigar'] == 'prince':
                prince_house = i
            if 'Smoothie' in house and house['Smoothie'] == 'desert':
                desert_house = i
        if prince_house is not None and desert_house is not None and prince_house != desert_house:
            return False
        for i in range(5):
            if 'Cigar' in assignment[i] and assignment[i]['Cigar'] == 'prince':
                if 'Smoothie' in assignment[i] and assignment[i]['Smoothie'] != 'desert':
                    return False
            if 'Smoothie' in assignment[i] and assignment[i]['Smoothie'] == 'desert':
                if 'Cigar' in assignment[i] and assignment[i]['Cigar'] != 'prince':
                    return False
        return True

    def c2(assignment):
        eric = None
        alice = None
        for i, house in enumerate(assignment):
            if 'Name' in house:
                if house['Name'] == 'Eric':
                    eric = i
                elif house['Name'] == 'Alice':
                    alice = i
        if eric is not None and alice is not None:
            if abs(eric - alice) != 2:
                return False
        return True

    def c3(assignment):
        short_house = None
        blends_house = None
        for i, house in enumerate(assignment):
            if 'Height' in house and house['Height'] == 'short':
                short_house = i
            if 'Cigar' in house and house['Cigar'] == 'blends':
                blends_house = i
        if short_house is not None and blends_house is not None and short_house != blends_house:
            return False
        for i in range(5):
            if 'Height' in assignment[i] and assignment[i]['Height'] == 'short':
                if 'Cigar' in assignment[i] and assignment[i]['Cigar'] != 'blends':
                    return False
            if 'Cigar' in assignment[i] and assignment[i]['Cigar'] == 'blends':
                if 'Height' in assignment[i] and assignment[i]['Height'] != 'short':
                    return False
        return True

    def c4(assignment):
        for i in range(4):
            if 'Phone' in assignment[i] and assignment[i]['Phone'] == 'iphone 13':
                if i+1 < 5:
                    if 'Cigar' in assignment[i+1] and assignment[i+1]['Cigar'] != 'blue master':
                        return False
        for i in range(1,5):
            if 'Cigar' in assignment[i] and assignment[i]['Cigar'] == 'blue master':
                if 'Phone' in assignment[i-1] and assignment[i-1]['Phone'] != 'iphone 13':
                    return False
        return True

    def c5(assignment):
        avg_house = None
        dunhill_house = None
        for i, house in enumerate(assignment):
            if 'Height' in house and house['Height'] == 'average':
                avg_house = i
            if 'Cigar' in house and house['Cigar'] == 'dunhill':
                dunhill_house = i
        if avg_house is not None and dunhill_house is not None and avg_house != dunhill_house:
            return False
        for i in range(5):
            if 'Height' in assignment[i] and assignment[i]['Height'] == 'average':
                if 'Cigar' in assignment[i] and assignment[i]['Cigar'] != 'dunhill':
                    return False
            if 'Cigar' in assignment[i] and assignment[i]['Cigar'] == 'dunhill':
                if 'Height' in assignment[i] and assignment[i]['Height'] != 'average':
                    return False
        return True

    def c6(assignment):
        for i in range(5):
            if 'Name' in assignment[i] and assignment[i]['Name'] == 'Eric':
                if 'Height' in assignment[i] and assignment[i]['Height'] != 'very tall':
                    return False
            if 'Height' in assignment[i] and assignment[i]['Height'] == 'very tall':
                if 'Name' in assignment[i] and assignment[i]['Name'] != 'Eric':
                    return False
        return True

    def c7(assignment):
        for i in range(4):
            if 'Name' in assignment[i] and assignment[i]['Name'] == 'Arnold':
                if i+1 < 5:
                    if 'Phone' in assignment[i+1] and assignment[i+1]['Phone'] != 'huawei p50':
                        return False
        for i in range(1,5):
            if 'Phone' in assignment[i] and assignment[i]['Phone'] == 'huawei p50':
                if 'Name' in assignment[i-1] and assignment[i-1]['Name'] != 'Arnold':
                    return False
        return True

    def c8(assignment):
        if len(assignment) > 3:
            house3 = assignment[3]
            if 'Name' in house3 and house3['Name'] == 'Bob':
                return False
        return True

    def c9(assignment):
        for i in range(4):
            if 'Name' in assignment[i] and assignment[i]['Name'] == 'Eric':
                if i+1 < 5:
                    if 'Smoothie' in assignment[i+1] and assignment[i+1]['Smoothie'] != 'cherry':
                        return False
        for i in range(1,5):
            if 'Smoothie' in assignment[i] and assignment[i]['Smoothie'] == 'cherry':
                if 'Name' in assignment[i-1] and assignment[i-1]['Name'] != 'Eric':
                    return False
        return True

    def c10(assignment):
        for i in range(5):
            if 'Name' in assignment[i] and assignment[i]['Name'] == 'Bob':
                if 'Cigar' in assignment[i] and assignment[i]['Cigar'] != 'dunhill':
                    return False
            if 'Cigar' in assignment[i] and assignment[i]['Cigar'] == 'dunhill':
                if 'Name' in assignment[i] and assignment[i]['Name'] != 'Bob':
                    return False
        return True

    def c11(assignment):
        for i in range(5):
            if 'Name' in assignment[i] and assignment[i]['Name'] == 'Bob':
                if 'Smoothie' in assignment[i] and assignment[i]['Smoothie'] != 'dragonfruit':
                    return False
            if 'Smoothie' in assignment[i] and assignment[i]['Smoothie'] == 'dragonfruit':
                if 'Name' in assignment[i] and assignment[i]['Name'] != 'Bob':
                    return False
        return True

    def c12(assignment):
        iphone_house = None
        oneplus_house = None
        for i, house in enumerate(assignment):
            if 'Phone' in house:
                if house['Phone'] == 'iphone 13':
                    iphone_house = i
                elif house['Phone'] == 'oneplus 9':
                    oneplus_house = i
        if iphone_house is not None and oneplus_house is not None:
            if abs(iphone_house - oneplus_house) != 1:
                return False
        return True

    def c13(assignment):
        phone_house = None
        height_house = None
        for i, house in enumerate(assignment):
            if 'Phone' in house and house['Phone'] == 'samsung galaxy s21':
                phone_house = i
            if 'Height' in house and house['Height'] == 'short':
                height_house = i
        if phone_house is not None and height_house is not None and phone_house != height_house:
            return False
        for i in range(5):
            if 'Phone' in assignment[i] and assignment[i]['Phone'] == 'samsung galaxy s21':
                if 'Height' in assignment[i] and assignment[i]['Height'] != 'short':
                    return False
            if 'Height' in assignment[i] and assignment[i]['Height'] == 'short':
                if 'Phone' in assignment[i] and assignment[i]['Phone'] != 'samsung galaxy s21':
                    return False
        return True

    def c14(assignment):
        eric_house = None
        bob_house = None
        for i, house in enumerate(assignment):
            if 'Name' in house:
                if house['Name'] == 'Eric':
                    eric_house = i
                elif house['Name'] == 'Bob':
                    bob_house = i
        if eric_house is not None and bob_house is not None:
            if abs(eric_house - bob_house) != 3:
                return False
        return True

    def c15(assignment):
        for i in range(5):
            if 'Name' in assignment[i] and assignment[i]['Name'] == 'Eric':
                if 'Phone' in assignment[i] and assignment[i]['Phone'] != 'iphone 13':
                    return False
            if 'Phone' in assignment[i] and assignment[i]['Phone'] == 'iphone 13':
                if 'Name' in assignment[i] and assignment[i]['Name'] != 'Eric':
                    return False
        return True

    def c16(assignment):
        desert_house = None
        lime_house = None
        for i, house in enumerate(assignment):
            if 'Smoothie' in house:
                if house['Smoothie'] == 'desert':
                    desert_house = i
                elif house['Smoothie'] == 'lime':
                    lime_house = i
        if desert_house is not None and lime_house is not None:
            if desert_house >= lime_house:
                return False
        return True

    def c17(assignment):
        arnold_house = None
        very_short_house = None
        for i, house in enumerate(assignment):
            if 'Name' in house and house['Name'] == 'Arnold':
                arnold_house = i
            if 'Height' in house and house['Height'] == 'very short':
                very_short_house = i
        if arnold_house is not None and very_short_house is not None:
            if abs(arnold_house - very_short_house) != 1:
                return False
        return True

    constraints = [c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17]
    
    def check_all_constraints(assignment):
        for constraint in constraints:
            if not constraint(assignment):
                return False
        return True

    def propagate_single_house(domains, house_i, assignment):
        house = assignment[house_i]
        if 'Name' in house:
            name = house['Name']
            if name == 'Eric':
                if 'Height' not in house:
                    domains[house_i]['Height'] = {'very tall'}
                if 'Phone' not in house:
                    domains[house_i]['Phone'] = {'iphone 13'}
            elif name == 'Bob':
                if 'Cigar' not in house:
                    domains[house_i]['Cigar'] = {'dunhill'}
                if 'Smoothie' not in house:
                    domains[house_i]['Smoothie'] = {'dragonfruit'}
                if 'Height' not in house:
                    domains[house_i]['Height'] = {'average'}
        if 'Height' in house:
            height = house['Height']
            if height == 'very tall':
                if 'Name' not in house:
                    domains[house_i]['Name'] = {'Eric'}
                if 'Phone' not in house:
                    domains[house_i]['Phone'] = {'iphone 13'}
            elif height == 'average':
                if 'Name' not in house:
                    domains[house_i]['Name'] = {'Bob'}
                if 'Cigar' not in house:
                    domains[house_i]['Cigar'] = {'dunhill'}
                if 'Smoothie' not in house:
                    domains[house_i]['Smoothie'] = {'dragonfruit'}
            elif height == 'short':
                if 'Phone' not in house:
                    domains[house_i]['Phone'] = {'samsung galaxy s21'}
                if 'Cigar' not in house:
                    domains[house_i]['Cigar'] = {'blends'}
        if 'Cigar' in house:
            cigar = house['Cigar']
            if cigar == 'dunhill':
                if 'Name' not in house:
                    domains[house_i]['Name'] = {'Bob'}
                if 'Height' not in house:
                    domains[house_i]['Height'] = {'average'}
            elif cigar == 'blends':
                if 'Height' not in house:
                    domains[house_i]['Height'] = {'short'}
            elif cigar == 'prince':
                if 'Smoothie' not in house:
                    domains[house_i]['Smoothie'] = {'desert'}
        if 'Smoothie' in house:
            smoothie = house['Smoothie']
            if smoothie == 'dragonfruit':
                if 'Name' not in house:
                    domains[house_i]['Name'] = {'Bob'}
                if 'Height' not in house:
                    domains[house_i]['Height'] = {'average'}
            elif smoothie == 'desert':
                if 'Cigar' not in house:
                    domains[house_i]['Cigar'] = {'prince'}
        if 'Phone' in house:
            phone = house['Phone']
            if phone == 'iphone 13':
                if 'Name' not in house:
                    domains[house_i]['Name'] = {'Eric'}
                if 'Height' not in house:
                    domains[house_i]['Height'] = {'very tall'}
            elif phone == 'samsung galaxy s21':
                if 'Height' not in house:
                    domains[house_i]['Height'] = {'short'}

    def infer(assignment, domains, house_i):
        changed = True
        while changed:
            changed = False
            for attr in domains[house_i]:
                if attr not in assignment[house_i] and len(domains[house_i][attr]) == 1:
                    value = next(iter(domains[house_i][attr]))
                    assignment[house_i][attr] = value
                    for j in range(5):
                        if j != house_i and attr in domains[j] and value in domains[j][attr]:
                            domains[j][attr].remove(value)
                    changed = True
                    propagate_single_house(domains, house_i, assignment)

    def backtrack(assignment, domains):
        complete = True
        for house in assignment:
            if len(house) != len(attributes_list):
                complete = False
                break
        if complete:
            return assignment
        
        min_domain_size = float('inf')
        next_house = None
        next_attr = None
        for i in range(5):
            for attr in attributes_list:
                if attr not in assignment[i]:
                    domain_size = len(domains[i][attr])
                    if domain_size < min_domain_size:
                        min_domain_size = domain_size
                        next_house = i
                        next_attr = attr
        
        if next_house is None:
            return None
        
        for value in list(domains[next_house][next_attr]):
            assignment_copy = copy.deepcopy(assignment)
            domains_copy = copy.deepcopy(domains)
            
            assignment_copy[next_house][next_attr] = value
            domains_copy[next_house][next_attr] = {value}
            
            for j in range(5):
                if j != next_house and next_attr in domains_copy[j] and value in domains_copy[j][next_attr]:
                    domains_copy[j][next_attr].remove(value)
            
            propagate_single_house(domains_copy, next_house, assignment_copy)
            infer(assignment_copy, domains_copy, next_house)
            
            if not check_all_constraints(assignment_copy):
                continue
                
            result = backtrack(assignment_copy, domains_copy)
            if result is not None:
                return result
                
        return None

    initial_assignment = [dict() for _ in range(5)]
    initial_domains = []
    for i in range(5):
        initial_domains.append({})
        for attr, values in attributes_list.items():
            initial_domains[i][attr] = set(values)
    
    solution = backtrack(initial_assignment, initial_domains)
    
    if solution is None:
        print('No solution found')
        return
    
    output = {
        "solution": {
            "header": ["House", "Name", "Height", "Cigar", "Smoothie", "Phone"],
            "rows": []
        }
    }
    
    for i, house in enumerate(solution):
        row = [str(i+1)]
        for attr in ["Name", "Height", "Cigar", "Smoothie", "Phone"]:
            row.append(house[attr])
        output["solution"]["rows"].append(row)
    
    print(json.dumps(output, indent=4))

if __name__ == '__main__':
    main()