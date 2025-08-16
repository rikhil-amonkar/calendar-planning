import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    categories = {
        'Name': ['Peter', 'Arnold', 'Eric'],
        'CarModel': ['toyota camry', 'ford f150', 'tesla model 3'],
        'HouseStyle': ['ranch', 'colonial', 'victorian'],
        'Pet': ['cat', 'dog', 'fish'],
        'Occupation': ['engineer', 'doctor', 'teacher'],
        'Vacation': ['city', 'mountain', 'beach']
    }
    
    # Generate all possible permutations for each category
    name_perms = permutations(categories['Name'])
    car_perms = permutations(categories['CarModel'])
    style_perms = permutations(categories['HouseStyle'])
    pet_perms = permutations(categories['Pet'])
    occ_perms = permutations(categories['Occupation'])
    vac_perms = permutations(categories['Vacation'])
    
    # Iterate through all possible combinations
    for names in name_perms:
        for cars in car_perms:
            for styles in style_perms:
                for pets in pet_perms:
                    for occs in occ_perms:
                        for vacs in vac_perms:
                            # Create a solution dictionary
                            solution = {
                                1: {
                                    'Name': names[0],
                                    'CarModel': cars[0],
                                    'HouseStyle': styles[0],
                                    'Pet': pets[0],
                                    'Occupation': occs[0],
                                    'Vacation': vacs[0]
                                },
                                2: {
                                    'Name': names[1],
                                    'CarModel': cars[1],
                                    'HouseStyle': styles[1],
                                    'Pet': pets[1],
                                    'Occupation': occs[1],
                                    'Vacation': vacs[1]
                                },
                                3: {
                                    'Name': names[2],
                                    'CarModel': cars[2],
                                    'HouseStyle': styles[2],
                                    'Pet': pets[2],
                                    'Occupation': occs[2],
                                    'Vacation': vacs[2]
                                }
                            }
                            
                            # Check all constraints
                            # Clue 1: fish in house 1
                            if solution[1]['Pet'] != 'fish':
                                continue
                            
                            # Clue 2: toyota camry in house 2
                            if solution[2]['CarModel'] != 'toyota camry':
                                continue
                            
                            # Clue 3: mountain not in house 2
                            if solution[2]['Vacation'] == 'mountain':
                                continue
                            
                            # Clue 4: city not in house 2
                            if solution[2]['Vacation'] == 'city':
                                continue
                            
                            # Clue 5: ranch left of Peter
                            ranch_pos = None
                            peter_pos = None
                            for i in [1, 2, 3]:
                                if solution[i]['HouseStyle'] == 'ranch':
                                    ranch_pos = i
                                if solution[i]['Name'] == 'Peter':
                                    peter_pos = i
                            if ranch_pos is None or peter_pos is None or ranch_pos >= peter_pos:
                                continue
                            
                            # Clue 6: toyota camry directly left of colonial
                            if solution[2]['CarModel'] == 'toyota camry' and solution[3]['HouseStyle'] != 'colonial':
                                continue
                            
                            # Clue 7: Arnold has cat
                            for i in [1, 2, 3]:
                                if solution[i]['Name'] == 'Arnold' and solution[i]['Pet'] != 'cat':
                                    break
                            else:
                                pass  # All Arnolds have cats
                            else:
                                continue
                            
                            # Clue 8: Eric left of mountain
                            eric_pos = None
                            mountain_pos = None
                            for i in [1, 2, 3]:
                                if solution[i]['Name'] == 'Eric':
                                    eric_pos = i
                                if solution[i]['Vacation'] == 'mountain':
                                    mountain_pos = i
                            if eric_pos is None or mountain_pos is None or eric_pos >= mountain_pos:
                                continue
                            
                            # Clue 9: engineer not in house 3
                            if solution[3]['Occupation'] == 'engineer':
                                continue
                            
                            # Clue 10: tesla left of teacher
                            tesla_pos = None
                            teacher_pos = None
                            for i in [1, 2, 3]:
                                if solution[i]['CarModel'] == 'tesla model 3':
                                    tesla_pos = i
                                if solution[i]['Occupation'] == 'teacher':
                                    teacher_pos = i
                            if tesla_pos is None or teacher_pos is None or tesla_pos >= teacher_pos:
                                continue
                            
                            # Clue 11: dog owner is engineer
                            for i in [1, 2, 3]:
                                if solution[i]['Pet'] == 'dog' and solution[i]['Occupation'] != 'engineer':
                                    break
                                if solution[i]['Occupation'] == 'engineer' and solution[i]['Pet'] != 'dog':
                                    break
                            else:
                                pass  # All dogs are engineers and vice versa
                            else:
                                continue
                            
                            # If all constraints are satisfied, return the solution
                            output = {
                                "solution": {
                                    "header": ["House", "Name", "CarModel", "HouseStyle", "Pet", "Occupation", "Vacation"],
                                    "rows": [
                                        ["1", solution[1]['Name'], solution[1]['CarModel'], solution[1]['HouseStyle'], solution[1]['Pet'], solution[1]['Occupation'], solution[1]['Vacation']],
                                        ["2", solution[2]['Name'], solution[2]['CarModel'], solution[2]['HouseStyle'], solution[2]['Pet'], solution[2]['Occupation'], solution[2]['Vacation']],
                                        ["3", solution[3]['Name'], solution[3]['CarModel'], solution[3]['HouseStyle'], solution[3]['Pet'], solution[3]['Occupation'], solution[3]['Vacation']]
                                    ]
                                }
                            }
                            return json.dumps(output, indent=2)
    
    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())