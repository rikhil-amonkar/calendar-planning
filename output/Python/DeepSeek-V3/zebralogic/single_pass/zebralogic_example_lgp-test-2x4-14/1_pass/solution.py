import json
from itertools import permutations

def solve_puzzle():
    # Define all possible options for each category
    names = ['Eric', 'Arnold']
    house_styles = ['victorian', 'colonial']
    smoothies = ['cherry', 'desert']
    pets = ['dog', 'cat']
    
    # Generate all possible permutations for each house
    for name_perm in permutations(names):
        for style_perm in permutations(house_styles):
            for smoothie_perm in permutations(smoothies):
                for pet_perm in permutations(pets):
                    # Assign to houses
                    solution = {
                        1: {
                            'Name': name_perm[0],
                            'HouseStyle': style_perm[0],
                            'Smoothie': smoothie_perm[0],
                            'Pet': pet_perm[0]
                        },
                        2: {
                            'Name': name_perm[1],
                            'HouseStyle': style_perm[1],
                            'Smoothie': smoothie_perm[1],
                            'Pet': pet_perm[1]
                        }
                    }
                    
                    # Check constraints
                    # Constraint 1: Cherry smoothie owner owns a dog
                    cherry_dog = True
                    for house in [1, 2]:
                        if solution[house]['Smoothie'] == 'cherry' and solution[house]['Pet'] != 'dog':
                            cherry_dog = False
                            break
                    if not cherry_dog:
                        continue
                    
                    # Constraint 2: Victorian house owner owns a dog
                    victorian_dog = True
                    for house in [1, 2]:
                        if solution[house]['HouseStyle'] == 'victorian' and solution[house]['Pet'] != 'dog':
                            victorian_dog = False
                            break
                    if not victorian_dog:
                        continue
                    
                    # Constraint 3: Victorian house is left of Eric
                    victorian_left_eric = False
                    victorian_house = None
                    eric_house = None
                    for house in [1, 2]:
                        if solution[house]['HouseStyle'] == 'victorian':
                            victorian_house = house
                        if solution[house]['Name'] == 'Eric':
                            eric_house = house
                    if victorian_house is not None and eric_house is not None and victorian_house < eric_house:
                        victorian_left_eric = True
                    if not victorian_left_eric:
                        continue
                    
                    # If all constraints are satisfied, prepare the output
                    output = {
                        "solution": {
                            "header": ["House", "Name", "HouseStyle", "Smoothie", "Pet"],
                            "rows": [
                                ["1", solution[1]['Name'], solution[1]['HouseStyle'], solution[1]['Smoothie'], solution[1]['Pet']],
                                ["2", solution[2]['Name'], solution[2]['HouseStyle'], solution[2]['Smoothie'], solution[2]['Pet']]
                            ]
                        }
                    }
                    return output
    
    return {"solution": {"header": [], "rows": []}}

# Solve the puzzle and print the result
solution = solve_puzzle()
print(json.dumps(solution, indent=2))