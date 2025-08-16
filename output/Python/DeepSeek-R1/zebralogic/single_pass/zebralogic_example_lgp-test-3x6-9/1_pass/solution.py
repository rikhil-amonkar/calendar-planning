import itertools
import json

def generate_attr_with_fixed(domain, fixed_dict):
    n = 3
    free_indices = [i for i in range(n) if i not in fixed_dict]
    fixed_values = list(fixed_dict.values())
    free_values = [v for v in domain if v not in fixed_values]
    
    if len(free_indices) != len(free_values):
        return []
    
    perms = list(itertools.permutations(free_values))
    results = []
    for p in perms:
        arr = [None] * n
        for idx, val in fixed_dict.items():
            arr[idx] = val
        for i, idx in enumerate(free_indices):
            arr[idx] = p[i]
        results.append(arr)
    return results

def main():
    attributes = {
        'Name': ['Peter', 'Arnold', 'Eric'],
        'CarModel': ['toyota camry', 'ford f150', 'tesla model 3'],
        'HouseStyle': ['ranch', 'colonial', 'victorian'],
        'Pet': ['cat', 'dog', 'fish'],
        'Occupation': ['engineer', 'doctor', 'teacher'],
        'Vacation': ['city', 'mountain', 'beach']
    }
    
    fixed_assignments = {
        'Pet': {0: 'fish'},
        'CarModel': {1: 'toyota camry'},
        'HouseStyle': {2: 'colonial'},
        'Vacation': {1: 'beach'}
    }
    
    perms = {}
    for attr, domain in attributes.items():
        fixed_dict = fixed_assignments.get(attr, {})
        perms[attr] = generate_attr_with_fixed(domain, fixed_dict)
    
    for name_assign in perms['Name']:
        for car_assign in perms['CarModel']:
            for style_assign in perms['HouseStyle']:
                for pet_assign in perms['Pet']:
                    for occ_assign in perms['Occupation']:
                        for vac_assign in perms['Vacation']:
                            houses = []
                            for i in range(3):
                                house = {
                                    'House': str(i+1),
                                    'Name': name_assign[i],
                                    'CarModel': car_assign[i],
                                    'HouseStyle': style_assign[i],
                                    'Pet': pet_assign[i],
                                    'Occupation': occ_assign[i],
                                    'Vacation': vac_assign[i]
                                }
                                houses.append(house)
                            
                            if check_constraints(houses):
                                sol = {
                                    "solution": {
                                        "header": ["House", "Name", "CarModel", "HouseStyle", "Pet", "Occupation", "Vacation"],
                                        "rows": []
                                    }
                                }
                                for house in houses:
                                    sol['solution']['rows'].append([
                                        house['House'],
                                        house['Name'],
                                        house['CarModel'],
                                        house['HouseStyle'],
                                        house['Pet'],
                                        house['Occupation'],
                                        house['Vacation']
                                    ])
                                print(json.dumps(sol))
                                return
    print('{"error": "No solution found"}')

def check_constraints(houses):
    ranch_index = None
    peter_index = None
    for i, h in enumerate(houses):
        if h['HouseStyle'] == 'ranch':
            ranch_index = i
        if h['Name'] == 'Peter':
            peter_index = i
    if ranch_index is None or peter_index is None:
        return False
    if ranch_index >= peter_index:
        return False

    toyota_index = None
    colonial_index = None
    for i, h in enumerate(houses):
        if h['CarModel'] == 'toyota camry':
            toyota_index = i
        if h['HouseStyle'] == 'colonial':
            colonial_index = i
    if toyota_index is None or colonial_index is None:
        return False
    if colonial_index - toyota_index != 1:
        return False

    for h in houses:
        if h['Name'] == 'Arnold' and h['Pet'] != 'cat':
            return False

    eric_index = None
    mountain_index = None
    for i, h in enumerate(houses):
        if h['Name'] == 'Eric':
            eric_index = i
        if h['Vacation'] == 'mountain':
            mountain_index = i
    if eric_index is None or mountain_index is None:
        return False
    if eric_index >= mountain_index:
        return False

    if houses[2]['Occupation'] == 'engineer':
        return False

    tesla_index = None
    teacher_index = None
    for i, h in enumerate(houses):
        if h['CarModel'] == 'tesla model 3':
            tesla_index = i
        if h['Occupation'] == 'teacher':
            teacher_index = i
    if tesla_index is None or teacher_index is None:
        return False
    if tesla_index >= teacher_index:
        return False

    dog_house = None
    engineer_house = None
    for h in houses:
        if h['Pet'] == 'dog':
            dog_house = h
        if h['Occupation'] == 'engineer':
            engineer_house = h
    if dog_house is None or engineer_house is None:
        return False
    if dog_house != engineer_house:
        return False

    return True

if __name__ == '__main__':
    main()