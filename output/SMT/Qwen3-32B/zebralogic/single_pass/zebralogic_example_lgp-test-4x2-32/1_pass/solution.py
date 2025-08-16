from z3 import *
import json

def solve_puzzle():
    solver = Solver()

    # Define variables for name houses and pet owners
    peter_house = Int('peter_house')
    arnold_house = Int('arnold_house')
    eric_house = Int('eric_house')
    alice_house = Int('alice_house')

    bird_owner = Int('bird_owner')
    fish_owner = Int('fish_owner')
    dog_owner = Int('dog_owner')
    cat_owner = Int('cat_owner')

    # Add constraints for ranges
    for var in [peter_house, arnold_house, eric_house, alice_house,
                bird_owner, fish_owner, dog_owner, cat_owner]:
        solver.add(And(1 <= var, var <= 4))

    # Add distinct constraints for name houses and pet owners
    name_houses = [peter_house, arnold_house, eric_house, alice_house]
    pet_owners = [bird_owner, fish_owner, dog_owner, cat_owner]
    solver.add(Distinct(name_houses))
    solver.add(Distinct(pet_owners))

    # Add clue constraints
    solver.add(eric_house == bird_owner)  # Clue 3
    solver.add(arnold_house == fish_owner)  # Clue 6
    solver.add(Abs(peter_house - arnold_house) == 2)  # Clue 4
    solver.add(dog_owner > alice_house)  # Clue 1
    solver.add(eric_house != 1)  # Clue 2
    solver.add(alice_house != 1)  # Clue 5

    if solver.check() == sat:
        model = solver.model()

        # Extract values from the model
        ph_val = model.eval(peter_house).as_long()
        ah_val = model.eval(arnold_house).as_long()
        eh_val = model.eval(eric_house).as_long()
        alh_val = model.eval(alice_house).as_long()

        bird_val = model.eval(bird_owner).as_long()
        fish_val = model.eval(fish_owner).as_long()
        dog_val = model.eval(dog_owner).as_long()
        cat_val = model.eval(cat_owner).as_long()

        rows = []
        for h in range(1, 5):
            # Determine name
            if ph_val == h:
                name = 'Peter'
            elif ah_val == h:
                name = 'Arnold'
            elif eh_val == h:
                name = 'Eric'
            elif alh_val == h:
                name = 'Alice'
            else:
                name = 'Unknown'  # Should not happen

            # Determine pet
            if bird_val == h:
                pet = 'bird'
            elif fish_val == h:
                pet = 'fish'
            elif dog_val == h:
                pet = 'dog'
            elif cat_val == h:
                pet = 'cat'
            else:
                pet = 'Unknown'  # Should not happen

            rows.append([str(h), name, pet])

        solution = {
            "solution": {
                "header": ["House", "Name", "Pet"],
                "rows": rows
            }
        }

        return solution
    else:
        return {"solution": {"header": [], "rows": []}}  # No solution

# Generate and print the JSON-formatted solution
print(json.dumps(solve_puzzle(), indent=2))