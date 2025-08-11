import json
from itertools import permutations

def solve_puzzle():
    # Define the attributes
    houses = [1, 2, 3, 4]
    names = ['Peter', 'Arnold', 'Eric', 'Alice']
    pets = ['bird', 'fish', 'dog', 'cat']
    
    # Generate all possible permutations for names and pets
    for name_perm in permutations(names):
        for pet_perm in permutations(pets):
            solution = {
                1: {'Name': None, 'pet': None},
                2: {'Name': None, 'pet': None},
                3: {'Name': None, 'pet': None},
                4: {'Name': None, 'pet': None}
            }
            
            # Assign names and pets to houses
            for i in range(4):
                solution[i+1]['Name'] = name_perm[i]
                solution[i+1]['pet'] = pet_perm[i]
            
            # Check constraints
            # Constraint 2: Eric is not in the first house
            if solution[1]['Name'] == 'Eric':
                continue
            
            # Constraint 3: Eric keeps a bird
            eric_house = None
            for house in solution:
                if solution[house]['Name'] == 'Eric':
                    eric_house = house
                    break
            if solution[eric_house]['pet'] != 'bird':
                continue
            
            # Constraint 5: Alice is not in the first house
            if solution[1]['Name'] == 'Alice':
                continue
            
            # Constraint 6: Arnold has fish
            arnold_house = None
            for house in solution:
                if solution[house]['Name'] == 'Arnold':
                    arnold_house = house
                    break
            if solution[arnold_house]['pet'] != 'fish':
                continue
            
            # Constraint 4: One house between fish (Arnold) and Peter
            peter_house = None
            for house in solution:
                if solution[house]['Name'] == 'Peter':
                    peter_house = house
                    break
            if abs(arnold_house - peter_house) != 2:
                continue
            
            # Constraint 1: Dog is to the right of Alice
            alice_house = None
            dog_house = None
            for house in solution:
                if solution[house]['Name'] == 'Alice':
                    alice_house = house
                if solution[house]['pet'] == 'dog':
                    dog_house = house
            if dog_house <= alice_house:
                continue
            
            # If all constraints are satisfied, format the solution
            result = {
                "solution": {
                    "header": ["House", "Name", "pet"],
                    "rows": [
                        ["1", solution[1]['Name'], solution[1]['pet']],
                        ["2", solution[2]['Name'], solution[2]['pet']],
                        ["3", solution[3]['Name'], solution[3]['pet']],
                        ["4", solution[4]['Name'], solution[4]['pet']]
                    ]
                }
            }
            return result
    
    return {"solution": {}}

# Solve the puzzle and print the result
solution = solve_puzzle()
print(json.dumps(solution, indent=2))