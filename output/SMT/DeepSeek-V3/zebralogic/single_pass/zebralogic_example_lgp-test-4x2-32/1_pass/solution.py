from z3 import *

def solve_housing_problem():
    # Create a solver instance
    s = Solver()

    # Define the houses
    houses = [1, 2, 3, 4]

    # Define the names and pets
    names = ["Peter", "Arnold", "Eric", "Alice"]
    pets = ["bird", "fish", "dog", "cat"]

    # Create variables for each house's name and pet
    name_vars = [Int(f"name_{house}") for house in houses]
    pet_vars = [Int(f"pet_{house}") for house in houses]

    # Add constraints that names and pets are within their respective ranges
    for house in houses:
        s.add(And(name_vars[house-1] >= 0, name_vars[house-1] < len(names)))
        s.add(And(pet_vars[house-1] >= 0, pet_vars[house-1] < len(pets)))

    # All names and pets must be unique
    s.add(Distinct(name_vars))
    s.add(Distinct(pet_vars))

    # Clue 2: Eric is not in the first house
    s.add(name_vars[0] != names.index("Eric"))

    # Clue 3: Eric keeps a pet bird
    for house in houses:
        s.add(Implies(name_vars[house-1] == names.index("Eric"), pet_vars[house-1] == pets.index("bird")))

    # Clue 5: Alice is not in the first house
    s.add(name_vars[0] != names.index("Alice"))

    # Clue 1: The person who owns a dog is somewhere to the right of Alice
    # Find Alice's house and ensure dog is to her right
    alice_house = Int("alice_house")
    s.add(Or([And(name_vars[house-1] == names.index("Alice"), alice_house == house) for house in houses]))
    dog_house = Int("dog_house")
    s.add(Or([And(pet_vars[house-1] == pets.index("dog"), dog_house == house) for house in houses]))
    s.add(dog_house > alice_house)

    # Clue 6: Arnold is the person with an aquarium of fish
    for house in houses:
        s.add(Implies(name_vars[house-1] == names.index("Arnold"), pet_vars[house-1] == pets.index("fish")))

    # Clue 4: There is one house between the person with fish and Peter
    # Find fish house and Peter's house, and ensure |fish_house - peter_house| == 2
    fish_house = Int("fish_house")
    s.add(Or([And(pet_vars[house-1] == pets.index("fish"), fish_house == house) for house in houses]))
    peter_house = Int("peter_house")
    s.add(Or([And(name_vars[house-1] == names.index("Peter"), peter_house == house) for house in houses]))
    s.add(Or(fish_house - peter_house == 2, peter_house - fish_house == 2))

    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "Pet"],
                "rows": []
            }
        }
        for house in houses:
            name_idx = model.evaluate(name_vars[house-1]).as_long()
            pet_idx = model.evaluate(pet_vars[house-1]).as_long()
            solution["solution"]["rows"].append([
                str(house),
                names[name_idx],
                pets[pet_idx]
            ])
        return solution
    else:
        return {"solution": {"header": ["House", "Name", "Pet"], "rows": []}}

# Print the solution as JSON
import json
print(json.dumps(solve_housing_problem(), indent=2))