import json
from itertools import permutations

def solve_puzzle():
    # Define all possible options for each attribute
    names = ['Peter', 'Arnold', 'Eric']
    cars = ['toyota camry', 'ford f150', 'tesla model 3']
    house_styles = ['ranch', 'colonial', 'victorian']
    pets = ['cat', 'dog', 'fish']
    occupations = ['engineer', 'doctor', 'teacher']
    vacations = ['city', 'mountain', 'beach']
    
    # Generate all possible permutations for each house
    for name_perm in permutations(names):
        for car_perm in permutations(cars):
            for style_perm in permutations(house_styles):
                for pet_perm in permutations(pets):
                    for occ_perm in permutations(occupations):
                        for vac_perm in permutations(vacations):
                            # Assign each permutation to houses 1, 2, 3
                            solution = {
                                1: {
                                    'Name': name_perm[0],
                                    'car': car_perm[0],
                                    'house': style_perm[0],
                                    'pet': pet_perm[0],
                                    'occupation': occ_perm[0],
                                    'vacation': vac_perm[0]
                                },
                                2: {
                                    'Name': name_perm[1],
                                    'car': car_perm[1],
                                    'house': style_perm[1],
                                    'pet': pet_perm[1],
                                    'occupation': occ_perm[1],
                                    'vacation': vac_perm[1]
                                },
                                3: {
                                    'Name': name_perm[2],
                                    'car': car_perm[2],
                                    'house': style_perm[2],
                                    'pet': pet_perm[2],
                                    'occupation': occ_perm[2],
                                    'vacation': vac_perm[2]
                                }
                            }
                            
                            # Check all constraints
                            # Clue 1: fish in house 1
                            if solution[1]['pet'] != 'fish':
                                continue
                            
                            # Clue 2: toyota camry in house 2
                            if solution[2]['car'] != 'toyota camry':
                                continue
                            
                            # Clue 3: mountain not in house 2
                            if solution[2]['vacation'] == 'mountain':
                                continue
                            
                            # Clue 4: city not in house 2
                            if solution[2]['vacation'] == 'city':
                                continue
                            
                            # Clue 5: ranch left of Peter
                            ranch_pos = None
                            peter_pos = None
                            for i in [1, 2, 3]:
                                if solution[i]['house'] == 'ranch':
                                    ranch_pos = i
                                if solution[i]['Name'] == 'Peter':
                                    peter_pos = i
                            if ranch_pos is None or peter_pos is None or ranch_pos >= peter_pos:
                                continue
                            
                            # Clue 6: toyota camry directly left of colonial
                            if solution[2]['car'] == 'toyota camry' and solution[3]['house'] != 'colonial':
                                continue
                            
                            # Clue 7: Arnold has cat
                            for i in [1, 2, 3]:
                                if solution[i]['Name'] == 'Arnold' and solution[i]['pet'] != 'cat':
                                    break
                            else:
                                # Check that Arnold exists and has cat
                                arnold_found = False
                                for i in [1, 2, 3]:
                                    if solution[i]['Name'] == 'Arnold':
                                        arnold_found = True
                                        if solution[i]['pet'] != 'cat':
                                            break
                                else:
                                    if not arnold_found:
                                        continue
                            
                            # Clue 8: Eric left of mountain
                            eric_pos = None
                            mountain_pos = None
                            for i in [1, 2, 3]:
                                if solution[i]['Name'] == 'Eric':
                                    eric_pos = i
                                if solution[i]['vacation'] == 'mountain':
                                    mountain_pos = i
                            if eric_pos is None or mountain_pos is None or eric_pos >= mountain_pos:
                                continue
                            
                            # Clue 9: engineer not in house 3
                            if solution[3]['occupation'] == 'engineer':
                                continue
                            
                            # Clue 10: tesla left of teacher
                            tesla_pos = None
                            teacher_pos = None
                            for i in [1, 2, 3]:
                                if solution[i]['car'] == 'tesla model 3':
                                    tesla_pos = i
                                if solution[i]['occupation'] == 'teacher':
                                    teacher_pos = i
                            if tesla_pos is None or teacher_pos is None or tesla_pos >= teacher_pos:
                                continue
                            
                            # Clue 11: dog owner is engineer
                            for i in [1, 2, 3]:
                                if solution[i]['pet'] == 'dog' and solution[i]['occupation'] != 'engineer':
                                    break
                                if solution[i]['occupation'] == 'engineer' and solution[i]['pet'] != 'dog':
                                    break
                            else:
                                # If all checks passed, return the solution
                                result = {
                                    "solution": {
                                        "header": ["House", "Name", "car", "house", "pet", "occupation", "vacation"],
                                        "rows": [
                                            ["1", solution[1]['Name'], solution[1]['car'], solution[1]['house'], solution[1]['pet'], solution[1]['occupation'], solution[1]['vacation']],
                                            ["2", solution[2]['Name'], solution[2]['car'], solution[2]['house'], solution[2]['pet'], solution[2]['occupation'], solution[2]['vacation']],
                                            ["3", solution[3]['Name'], solution[3]['car'], solution[3]['house'], solution[3]['pet'], solution[3]['occupation'], solution[3]['vacation']]
                                        ]
                                    }
                                }
                                return json.dumps(result, indent=2)
    return json.dumps({"error": "No solution found"}, indent=2)

print(solve_puzzle())