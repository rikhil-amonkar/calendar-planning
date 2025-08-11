import itertools
import json

def solve_puzzle():
    # Define all possible categories and options
    categories = {
        'House': ['1', '2', '3'],
        'Name': ['Arnold', 'Eric', 'Peter'],
        'Flower': ['carnations', 'lilies', 'daffodils'],
        'Hair Color': ['black', 'brown', 'blonde'],
        'Sport': ['soccer', 'basketball', 'tennis'],
        'House Style': ['colonial', 'ranch', 'victorian'],
        'Pet': ['fish', 'dog', 'cat']
    }
    
    # Generate all possible permutations for each category except House (fixed order)
    from itertools import permutations
    name_perms = permutations(categories['Name'])
    flower_perms = permutations(categories['Flower'])
    hair_perms = permutations(categories['Hair Color'])
    sport_perms = permutations(categories['Sport'])
    style_perms = permutations(categories['House Style'])
    pet_perms = permutations(categories['Pet'])
    
    # Iterate through all possible combinations
    for names in name_perms:
        for flowers in flower_perms:
            for hairs in hair_perms:
                for sports in sport_perms:
                    for styles in style_perms:
                        for pets in pet_perms:
                            # Create a solution dictionary
                            solution = {
                                '1': {
                                    'Name': names[0],
                                    'Flower': flowers[0],
                                    'Hair Color': hairs[0],
                                    'Sport': sports[0],
                                    'House Style': styles[0],
                                    'Pet': pets[0]
                                },
                                '2': {
                                    'Name': names[1],
                                    'Flower': flowers[1],
                                    'Hair Color': hairs[1],
                                    'Sport': sports[1],
                                    'House Style': styles[1],
                                    'Pet': pets[1]
                                },
                                '3': {
                                    'Name': names[2],
                                    'Flower': flowers[2],
                                    'Hair Color': hairs[2],
                                    'Sport': sports[2],
                                    'House Style': styles[2],
                                    'Pet': pets[2]
                                }
                            }
                            
                            # Check all constraints
                            # Clue 2: The person who has blonde hair is in the second house.
                            if solution['2']['Hair Color'] != 'blonde':
                                continue
                            
                            # Clue 3: The person who loves daffodils has blonde hair.
                            if solution['2']['Flower'] != 'daffodils':
                                continue
                            
                            # Clue 8: The person who loves soccer is in the third house.
                            if solution['3']['Sport'] != 'soccer':
                                continue
                            
                            # Clue 1: The person who has a cat loves soccer.
                            if solution['3']['Pet'] != 'cat':
                                continue
                            
                            # Clue 4: Peter loves basketball.
                            peter_found = False
                            for house in ['1', '2', '3']:
                                if solution[house]['Name'] == 'Peter' and solution[house]['Sport'] == 'basketball':
                                    peter_found = True
                                    break
                            if not peter_found:
                                continue
                            
                            # Clue 6: The person who owns a dog loves basketball.
                            dog_found = False
                            for house in ['1', '2', '3']:
                                if solution[house]['Pet'] == 'dog' and solution[house]['Sport'] == 'basketball':
                                    dog_found = True
                                    break
                            if not dog_found:
                                continue
                            
                            # Clue 5: Arnold is directly left of the person in a ranch-style home.
                            arnold_pos = None
                            ranch_pos = None
                            for house in ['1', '2', '3']:
                                if solution[house]['Name'] == 'Arnold':
                                    arnold_pos = int(house)
                                if solution[house]['House Style'] == 'ranch':
                                    ranch_pos = int(house)
                            if arnold_pos is None or ranch_pos is None or ranch_pos != arnold_pos + 1:
                                continue
                            
                            # Clue 7: The person who loves carnations is directly left of the person who has blonde hair.
                            # Blonde hair is in house 2, so carnations must be in house 1
                            if solution['1']['Flower'] != 'carnations':
                                continue
                            
                            # Clue 9: Arnold is somewhere to the left of the person who has black hair.
                            arnold_pos = None
                            black_pos = None
                            for house in ['1', '2', '3']:
                                if solution[house]['Name'] == 'Arnold':
                                    arnold_pos = int(house)
                                if solution[house]['Hair Color'] == 'black':
                                    black_pos = int(house)
                            if arnold_pos is None or black_pos is None or arnold_pos >= black_pos:
                                continue
                            
                            # Clue 10: The person in a colonial-style house is in the third house.
                            if solution['3']['House Style'] != 'colonial':
                                continue
                            
                            # All constraints satisfied, return the solution
                            result = {
                                "solution": {
                                    "header": ["House", "Name", "Flower", "Hair Color", "Sport", "House Style", "Pet"],
                                    "rows": [
                                        ["1", solution['1']['Name'], solution['1']['Flower'], solution['1']['Hair Color'], solution['1']['Sport'], solution['1']['House Style'], solution['1']['Pet']],
                                        ["2", solution['2']['Name'], solution['2']['Flower'], solution['2']['Hair Color'], solution['2']['Sport'], solution['2']['House Style'], solution['2']['Pet']],
                                        ["3", solution['3']['Name'], solution['3']['Flower'], solution['3']['Hair Color'], solution['3']['Sport'], solution['3']['House Style'], solution['3']['Pet']]
                                    ]
                                }
                            }
                            return result
    return {"solution": {"header": [], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))