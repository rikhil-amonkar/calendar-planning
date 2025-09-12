from z3 import *

def solve_puzzle():
    # Define the domains
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Arnold", "Eric", "Bob", "Alice", "Carol", "Peter"]
    mothers = ["Sarah", "Holly", "Janelle", "Aniya", "Penny", "Kailyn"]
    pets = ["hamster", "dog", "bird", "cat", "fish", "rabbit"]

    # Create variables
    name_vars = {house: Int(f'name_{house}') for house in houses}
    mother_vars = {house: Int(f'mother_{house}') for house in houses}
    pet_vars = {house: Int(f'pet_{house}') for house in houses}

    # Create solver
    solver = Solver()

    # Add domain constraints
    for house in houses:
        solver.add(name_vars[house] >= 0)
        solver.add(name_vars[house] < len(names))
        solver.add(mother_vars[house] >= 0)
        solver.add(mother_vars[house] < len(mothers))
        solver.add(pet_vars[house] >= 0)
        solver.add(pet_vars[house] < len(pets))

    # All names, mothers, and pets must be unique
    solver.add(Distinct([name_vars[house] for house in houses]))
    solver.add(Distinct([mother_vars[house] for house in houses]))
    solver.add(Distinct([pet_vars[house] for house in houses]))

    # Clue constraints
    # 1. Bob is not in the second house.
    solver.add(name_vars[2] != names.index("Bob"))

    # 2. There are two houses between the person who has a cat and the person who owns a rabbit.
    cat_house = Int('cat_house')
    rabbit_house = Int('rabbit_house')
    solver.add(Or(cat_house + 3 == rabbit_house, rabbit_house + 3 == cat_house))
    solver.add(And(cat_house >= 1, cat_house <= 6))
    solver.add(And(rabbit_house >= 1, rabbit_house <= 6))
    solver.add(pet_vars[cat_house] == pets.index("cat"))
    solver.add(pet_vars[rabbit_house] == pets.index("rabbit"))

    # 3. The person who has a cat is directly left of The person whose mother's name is Holly.
    solver.add(mother_vars[cat_house + 1] == mothers.index("Holly"))

    # 4. The person with a pet hamster is directly left of the person who owns a rabbit.
    hamster_house = Int('hamster_house')
    solver.add(hamster_house + 1 == rabbit_house)
    solver.add(And(hamster_house >= 1, hamster_house <= 5))
    solver.add(pet_vars[hamster_house] == pets.index("hamster"))

    # 5. The person who owns a rabbit is Eric.
    solver.add(name_vars[rabbit_house] == names.index("Eric"))

    # 6. There is one house between the person who owns a dog and the person who has a cat.
    dog_house = Int('dog_house')
    solver.add(Or(dog_house + 2 == cat_house, cat_house + 2 == dog_house))
    solver.add(And(dog_house >= 1, dog_house <= 6))
    solver.add(pet_vars[dog_house] == pets.index("dog"))

    # 7. The person who has a cat is The person whose mother's name is Janelle.
    solver.add(mother_vars[cat_house] == mothers.index("Janelle"))

    # 8. Alice is directly left of Carol.
    alice_house = Int('alice_house')
    carol_house = Int('carol_house')
    solver.add(alice_house + 1 == carol_house)
    solver.add(And(alice_house >= 1, alice_house <= 5))
    solver.add(name_vars[alice_house] == names.index("Alice"))
    solver.add(name_vars[carol_house] == names.index("Carol"))

    # 9. Carol is The person whose mother's name is Aniya.
    solver.add(mother_vars[carol_house] == mothers.index("Aniya"))

    # 10. Arnold is the person who has a cat.
    solver.add(name_vars[cat_house] == names.index("Arnold"))

    # 11. The person whose mother's name is Kailyn is the person who owns a rabbit.
    solver.add(mother_vars[rabbit_house] == mothers.index("Kailyn"))

    # 12. The person with an aquarium of fish is The person whose mother's name is Sarah.
    fish_house = Int('fish_house')
    solver.add(pet_vars[fish_house] == pets.index("fish"))
    solver.add(mother_vars[fish_house] == mothers.index("Sarah"))

    # Check if the problem is solvable
    if solver.check() == sat:
        model = solver.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "Mother", "Pet"],
                "rows": []
            }
        }
        for house in houses:
            name = names[model.evaluate(name_vars[house]).as_long()]
            mother = mothers[model.evaluate(mother_vars[house]).as_long()]
            pet = pets[model.evaluate(pet_vars[house]).as_long()]
            solution["solution"]["rows"].append([str(house), name, mother, pet])
        return solution
    else:
        return None

# Solve the puzzle and print the solution in JSON format
import json
solution = solve_puzzle()
if solution:
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")