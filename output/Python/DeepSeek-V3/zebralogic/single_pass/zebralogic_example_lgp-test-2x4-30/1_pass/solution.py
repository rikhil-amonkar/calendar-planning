import json
from itertools import permutations

def solve_puzzle():
    # Define the attributes and their possible values
    attributes = {
        'Name': ['Arnold', 'Eric'],
        'Hair color': ['black', 'brown'],
        'Favorite sport': ['basketball', 'soccer'],
        'Favorite smoothie': ['desert', 'cherry']
    }
    
    # Generate all possible permutations for each attribute
    name_perms = permutations(attributes['Name'])
    hair_perms = permutations(attributes['Hair color'])
    sport_perms = permutations(attributes['Favorite sport'])
    smoothie_perms = permutations(attributes['Favorite smoothie'])
    
    # Iterate through all possible combinations
    for names in name_perms:
        for hairs in hair_perms:
            for sports in sport_perms:
                for smoothies in smoothie_perms:
                    # Create the house assignments
                    solution = {
                        1: {
                            'Name': names[0],
                            'Hair color': hairs[0],
                            'Favorite sport': sports[0],
                            'Favorite smoothie': smoothies[0]
                        },
                        2: {
                            'Name': names[1],
                            'Hair color': hairs[1],
                            'Favorite sport': sports[1],
                            'Favorite smoothie': smoothies[1]
                        }
                    }
                    
                    # Check all constraints
                    # Constraint 1: The Desert smoothie lover is Arnold.
                    constraint1 = True
                    for house in [1, 2]:
                        if solution[house]['Favorite smoothie'] == 'desert' and solution[house]['Name'] != 'Arnold':
                            constraint1 = False
                            break
                    if not constraint1:
                        continue
                    
                    # Constraint 2: The person who has brown hair is the person who loves basketball.
                    constraint2 = True
                    for house in [1, 2]:
                        if solution[house]['Hair color'] == 'brown' and solution[house]['Favorite sport'] != 'basketball':
                            constraint2 = False
                            break
                        if solution[house]['Favorite sport'] == 'basketball' and solution[house]['Hair color'] != 'brown':
                            constraint2 = False
                            break
                    if not constraint2:
                        continue
                    
                    # Constraint 3: Arnold is somewhere to the left of the person who has black hair.
                    arnold_house = None
                    black_hair_house = None
                    for house in [1, 2]:
                        if solution[house]['Name'] == 'Arnold':
                            arnold_house = house
                        if solution[house]['Hair color'] == 'black':
                            black_hair_house = house
                    if arnold_house is None or black_hair_house is None or arnold_house >= black_hair_house:
                        continue
                    
                    # If all constraints are satisfied, format the solution
                    header = ['House', 'Name', 'Hair color', 'Favorite sport', 'Favorite smoothie']
                    rows = [
                        ['1', solution[1]['Name'], solution[1]['Hair color'], solution[1]['Favorite sport'], solution[1]['Favorite smoothie']],
                        ['2', solution[2]['Name'], solution[2]['Hair color'], solution[2]['Favorite sport'], solution[2]['Favorite smoothie']]
                    ]
                    
                    output = {
                        'solution': {
                            'header': header,
                            'rows': rows
                        }
                    }
                    
                    return json.dumps(output, indent=2)
    
    return json.dumps({'solution': {}})

print(solve_puzzle())