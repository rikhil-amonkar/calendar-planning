import json
from itertools import permutations

def solve_puzzle():
    names = ['Peter', 'Arnold', 'Eric', 'Alice']
    pets = ['bird', 'fish', 'dog', 'cat']
    houses = [1, 2, 3, 4]
    
    # Generate all possible permutations for names and pets
    for name_perm in permutations(names):
        for pet_perm in permutations(pets):
            solution = {
                1: {'Name': name_perm[0], 'Pet': pet_perm[0]},
                2: {'Name': name_perm[1], 'Pet': pet_perm[1]},
                3: {'Name': name_perm[2], 'Pet': pet_perm[2]},
                4: {'Name': name_perm[3], 'Pet': pet_perm[3]}
            }
            
            # Check all constraints
            # 1. The person who owns a dog is somewhere to the right of Alice.
            alice_house = None
            dog_house = None
            for house in houses:
                if solution[house]['Name'] == 'Alice':
                    alice_house = house
                if solution[house]['Pet'] == 'dog':
                    dog_house = house
            if alice_house is not None and dog_house is not None:
                if dog_house <= alice_house:
                    continue
            elif dog_house is None:
                continue  # no dog in solution
            
            # 2. Eric is not in the first house.
            if solution[1]['Name'] == 'Eric':
                continue
                
            # 3. Eric is the person who keeps a pet bird.
            eric_house = None
            for house in houses:
                if solution[house]['Name'] == 'Eric':
                    eric_house = house
                    if solution[house]['Pet'] != 'bird':
                        break
            else:
                if eric_house is None:
                    continue  # no Eric in solution
            if eric_house is not None and solution[eric_house]['Pet'] != 'bird':
                continue
                
            # 4. There is one house between the person with an aquarium of fish and Peter.
            fish_house = None
            peter_house = None
            for house in houses:
                if solution[house]['Pet'] == 'fish':
                    fish_house = house
                if solution[house]['Name'] == 'Peter':
                    peter_house = house
            if fish_house is not None and peter_house is not None:
                if abs(fish_house - peter_house) != 2:
                    continue
            else:
                continue  # missing fish or Peter
                
            # 5. Alice is not in the first house.
            if solution[1]['Name'] == 'Alice':
                continue
                
            # 6. Arnold is the person with an aquarium of fish.
            arnold_house = None
            for house in houses:
                if solution[house]['Name'] == 'Arnold':
                    arnold_house = house
                    if solution[house]['Pet'] != 'fish':
                        break
            else:
                if arnold_house is None:
                    continue  # no Arnold in solution
            if arnold_house is not None and solution[arnold_house]['Pet'] != 'fish':
                continue
                
            # If all constraints are satisfied, return the solution
            result = {
                "solution": {
                    "header": ["House", "Name", "Pet"],
                    "rows": [
                        ["1", solution[1]['Name'], solution[1]['Pet']],
                        ["2", solution[2]['Name'], solution[2]['Pet']],
                        ["3", solution[3]['Name'], solution[3]['Pet']],
                        ["4", solution[4]['Name'], solution[4]['Pet']]
                    ]
                }
            }
            return result
    
    return {"solution": {"header": ["House", "Name", "Pet"], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))