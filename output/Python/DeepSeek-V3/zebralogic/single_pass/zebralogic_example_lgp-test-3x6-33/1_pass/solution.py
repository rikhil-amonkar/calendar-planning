import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    categories = {
        'Name': ['Arnold', 'Eric', 'Peter'],
        'Flower': ['carnations', 'lilies', 'daffodils'],
        'HairColor': ['black', 'brown', 'blonde'],
        'FavoriteSport': ['soccer', 'basketball', 'tennis'],
        'HouseStyle': ['colonial', 'ranch', 'victorian'],
        'Pet': ['fish', 'dog', 'cat']
    }
    
    # Initialize houses
    houses = [1, 2, 3]
    
    # Generate all possible permutations for each category
    name_perms = permutations(categories['Name'])
    flower_perms = permutations(categories['Flower'])
    hair_perms = permutations(categories['HairColor'])
    sport_perms = permutations(categories['FavoriteSport'])
    style_perms = permutations(categories['HouseStyle'])
    pet_perms = permutations(categories['Pet'])
    
    # Iterate through all possible combinations to find the solution
    for names in name_perms:
        for flowers in flower_perms:
            for hairs in hair_perms:
                for sports in sport_perms:
                    for styles in style_perms:
                        for pets in pet_perms:
                            # Assign values to each house
                            solution = {
                                1: {
                                    'Name': names[0],
                                    'Flower': flowers[0],
                                    'HairColor': hairs[0],
                                    'FavoriteSport': sports[0],
                                    'HouseStyle': styles[0],
                                    'Pet': pets[0]
                                },
                                2: {
                                    'Name': names[1],
                                    'Flower': flowers[1],
                                    'HairColor': hairs[1],
                                    'FavoriteSport': sports[1],
                                    'HouseStyle': styles[1],
                                    'Pet': pets[1]
                                },
                                3: {
                                    'Name': names[2],
                                    'Flower': flowers[2],
                                    'HairColor': hairs[2],
                                    'FavoriteSport': sports[2],
                                    'HouseStyle': styles[2],
                                    'Pet': pets[2]
                                }
                            }
                            
                            # Check all constraints
                            # Clue 8: The person who loves soccer is in the third house.
                            if solution[3]['FavoriteSport'] != 'soccer':
                                continue
                            
                            # Clue 1: The person who has a cat is the person who loves soccer.
                            if solution[3]['Pet'] != 'cat':
                                continue
                            
                            # Clue 2: The person who has blonde hair is in the second house.
                            if solution[2]['HairColor'] != 'blonde':
                                continue
                            
                            # Clue 3: The person who loves daffodils has blonde hair.
                            if solution[2]['Flower'] != 'daffodils':
                                continue
                            
                            # Clue 4: Peter loves basketball.
                            peter_found = False
                            for house in solution.values():
                                if house['Name'] == 'Peter' and house['FavoriteSport'] == 'basketball':
                                    peter_found = True
                                    break
                            if not peter_found:
                                continue
                            
                            # Clue 5: Arnold is directly left of the person in a ranch-style home.
                            arnold_pos = None
                            ranch_pos = None
                            for i in houses:
                                if solution[i]['Name'] == 'Arnold':
                                    arnold_pos = i
                                if solution[i]['HouseStyle'] == 'ranch':
                                    ranch_pos = i
                            if arnold_pos is None or ranch_pos is None or ranch_pos != arnold_pos + 1:
                                continue
                            
                            # Clue 6: The person who owns a dog loves basketball.
                            dog_found = False
                            for house in solution.values():
                                if house['Pet'] == 'dog' and house['FavoriteSport'] == 'basketball':
                                    dog_found = True
                                    break
                            if not dog_found:
                                continue
                            
                            # Clue 7: The person who loves carnations is directly left of the person who has blonde hair.
                            carn_pos = None
                            blonde_pos = 2  # From clue 2
                            for i in houses:
                                if solution[i]['Flower'] == 'carnations':
                                    carn_pos = i
                            if carn_pos is None or carn_pos + 1 != blonde_pos:
                                continue
                            
                            # Clue 9: Arnold is somewhere to the left of the person who has black hair.
                            arnold_pos = None
                            black_pos = None
                            for i in houses:
                                if solution[i]['Name'] == 'Arnold':
                                    arnold_pos = i
                                if solution[i]['HairColor'] == 'black':
                                    black_pos = i
                            if arnold_pos is None or black_pos is None or arnold_pos >= black_pos:
                                continue
                            
                            # Clue 10: The person in a colonial-style house is in the third house.
                            if solution[3]['HouseStyle'] != 'colonial':
                                continue
                            
                            # If all constraints are satisfied, return the solution
                            result = {
                                "solution": {
                                    "header": ["House", "Name", "Flower", "HairColor", "FavoriteSport", "HouseStyle", "Pet"],
                                    "rows": [
                                        ["1", solution[1]['Name'], solution[1]['Flower'], solution[1]['HairColor'], solution[1]['FavoriteSport'], solution[1]['HouseStyle'], solution[1]['Pet']],
                                        ["2", solution[2]['Name'], solution[2]['Flower'], solution[2]['HairColor'], solution[2]['FavoriteSport'], solution[2]['HouseStyle'], solution[2]['Pet']],
                                        ["3", solution[3]['Name'], solution[3]['Flower'], solution[3]['HairColor'], solution[3]['FavoriteSport'], solution[3]['HouseStyle'], solution[3]['Pet']]
                                    ]
                                }
                            }
                            return json.dumps(result, indent=2)
    
    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())