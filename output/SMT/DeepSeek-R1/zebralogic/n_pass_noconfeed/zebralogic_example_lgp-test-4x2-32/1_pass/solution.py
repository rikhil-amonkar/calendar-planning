import json
from z3 import *

def main():
    # Define the attributes
    names = ['Peter', 'Arnold', 'Eric', 'Alice']
    pets = ['bird', 'fish', 'dog', 'cat']
    
    # Create mappings to integers
    name_to_int = {name: i for i, name in enumerate(names)}
    pet_to_int = {pet: i for i, pet in enumerate(pets)}
    
    # Create solver
    solver = Solver()
    
    # Create variables for each house: name and pet as integers
    n = [Int(f'n_{i}') for i in range(4)]
    p = [Int(f'p_{i}') for i in range(4)]
    
    # Constraints: each name and pet variable must be in [0,3]
    for i in range(4):
        solver.add(And(n[i] >= 0, n[i] < 4))
        solver.add(And(p[i] >= 0, p[i] < 4))
    
    # All names and pets are distinct
    solver.add(Distinct(n))
    solver.add(Distinct(p))
    
    # Clue 2: Eric is not in the first house
    solver.add(n[0] != name_to_int['Eric'])
    
    # Clue 3: Eric keeps a pet bird
    for i in range(4):
        solver.add(Implies(n[i] == name_to_int['Eric'], p[i] == pet_to_int['bird']))
    
    # Clue 5: Alice is not in the first house
    solver.add(n[0] != name_to_int['Alice'])
    
    # Clue 6: Arnold has the fish
    for i in range(4):
        solver.add(Implies(n[i] == name_to_int['Arnold'], p[i] == pet_to_int['fish']))
    
    # Clue 1: Dog owner is right of Alice
    # Find Alice's house index
    alice_house = Int('alice_house')
    solver.add(alice_house >= 0, alice_house < 4)
    for i in range(4):
        solver.add(Implies(n[i] == name_to_int['Alice'], alice_house == i))
    
    dog_house = Int('dog_house')
    solver.add(dog_house >= 0, dog_house < 4)
    for i in range(4):
        solver.add(Implies(p[i] == pet_to_int['dog'], dog_house == i))
    
    solver.add(dog_house > alice_house)
    
    # Clue 4: One house between fish and Peter
    fish_house = Int('fish_house')
    solver.add(fish_house >= 0, fish_house < 4)
    for i in range(4):
        solver.add(Implies(p[i] == pet_to_int['fish'], fish_house == i))
    
    peter_house = Int('peter_house')
    solver.add(peter_house >= 0, peter_house < 4)
    for i in range(4):
        solver.add(Implies(n[i] == name_to_int['Peter'], peter_house == i))
    
    solver.add(Or(fish_house - peter_house == 2, peter_house - fish_house == 2))
    
    # Check for solution
    if solver.check() == sat:
        model = solver.model()
        
        # Build the solution
        rows = []
        for i in range(4):
            name_val = model.eval(n[i]).as_long()
            pet_val = model.eval(p[i]).as_long()
            rows.append([str(i+1), names[name_val], pets[pet_val]])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Pet"],
                "rows": rows
            }
        }
        
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()