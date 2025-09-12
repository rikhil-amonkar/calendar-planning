import z3
import json

def main():
    # Create solver
    solver = z3.Solver()
    
    # House positions
    houses = [1, 2, 3, 4]
    
    # Define variables for each attribute
    name_vars = {name: z3.Int(f'name_{name}') for name in ['Peter', 'Arnold', 'Eric', 'Alice']}
    pet_vars = {pet: z3.Int(f'pet_{pet}') for pet in ['bird', 'fish', 'dog', 'cat']}
    
    # All names and pets must be in different houses (1-4)
    solver.add(z3.Distinct(list(name_vars.values())))
    solver.add(z3.Distinct(list(pet_vars.values())))
    
    # All variables must be between 1 and 4
    for var in list(name_vars.values()) + list(pet_vars.values()):
        solver.add(var >= 1, var <= 4)
    
    # Clue 1: The person who owns a dog is somewhere to the right of Alice.
    solver.add(pet_vars['dog'] > name_vars['Alice'])
    
    # Clue 2: Eric is not in the first house.
    solver.add(name_vars['Eric'] != 1)
    
    # Clue 3: Eric is the person who keeps a pet bird.
    solver.add(name_vars['Eric'] == pet_vars['bird'])
    
    # Clue 4: There is one house between the person with an aquarium of fish and Peter.
    solver.add(z3.Or(
        pet_vars['fish'] == name_vars['Peter'] + 2,
        pet_vars['fish'] == name_vars['Peter'] - 2
    ))
    
    # Clue 5: Alice is not in the first house.
    solver.add(name_vars['Alice'] != 1)
    
    # Clue 6: Arnold is the person with an aquarium of fish.
    solver.add(name_vars['Arnold'] == pet_vars['fish'])
    
    # Check if solution exists
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Create result structure
        result = {
            "solution": {
                "header": ["House", "Name", "Pet"],
                "rows": []
            }
        }
        
        # For each house, find the name and pet
        for house in houses:
            name = None
            pet = None
            
            # Find which name is in this house
            for n, var in name_vars.items():
                if model.eval(var).as_long() == house:
                    name = n
                    break
            
            # Find which pet is in this house
            for p, var in pet_vars.items():
                if model.eval(var).as_long() == house:
                    pet = p
                    break
            
            result["solution"]["rows"].append([str(house), name, pet])
        
        # Output as JSON
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()