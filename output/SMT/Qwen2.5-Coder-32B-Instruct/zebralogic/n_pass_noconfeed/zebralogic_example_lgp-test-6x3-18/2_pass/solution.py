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
    solver.add(Or([And(cat_house == h, pet_vars[h] == pets.index("cat")) for h in houses]))
    solver.add(Or([And(rabbit_house == h, pet_vars[h] == pets.index("rabbit")) for h in houses]))

    # 3. The person who has a cat is directly left of The person whose mother's name is Holly.
    solver.add(Or([And(cat_house == h, mother_vars[h + 1] == mothers.index("Holly")) for h in range(1, 6)]))

    # 4. The person with a pet hamster is directly left of the person who owns a rabbit.
    hamster_house = Int('hamster_house')
    solver.add(hamster_house + 1 == rabbit_house)
    solver.add(And(hamster_house >= 1, hamster_house <= 5))
    solver.add(Or([And(hamster_house == h, pet_vars[h] == pets.index("hamster")) for h in houses]))

    # 5. The person who owns a rabbit is Eric.
    solver.add(Or([And(rabbit_house == h, name_vars[h] == names.index("Eric")) for h in houses]))

    # 6. There is one house between the person who owns a dog and the person who has a cat.
    dog_house = Int('dog_house')
    solver.add(Or(dog_house + 2 == cat_house, cat_house + 2 == dog_house))
    solver.add(And(dog_house >= 1, dog_house <= 6))
    solver.add(Or([And(dog_house == h, pet_vars[h] == pets.index("dog")) for h in houses]))

    # 7. The person who has a cat is The person whose mother's name is Janelle.
    solver.add(Or([And(cat_house == h, mother_vars[h] == mothers.index("Janelle")) for h in houses]))

    # 8. Alice is directly left of Carol.
    alice_house = Int('alice_house')
    carol_house = Int('carol_house')
    solver.add(alice_house + 1 == carol_house)
    solver.add(And(alice_house >= 1, alice_house <= 5))
    solver.add(Or([And(alice_house == h, name_vars[h] == names.index("Alice")) for h in houses]))
    solver.add(Or([And(carol_house == h, name_vars[h] == names.index("Carol")) for h in houses]))

    # 9. Carol is The person whose mother's name is Aniya.
    solver.add(Or([And(carol_house == h, mother_vars[h] == mothers.index("Aniya")) for h in houses]))

    # 10. Arnold is the person who has a cat.
    solver.add(Or([And(cat_house == h, name_vars[h] == names.index("Arnold")) for h in houses]))

    # 11. The person whose mother's name is Kailyn is the person who owns a rabbit.
    solver.add(Or([And(rabbit_house == h, mother_vars[h] == mothers.index("Kailyn")) for h in houses]))

    # 12. The person with an aquarium of fish is The person whose mother's name is Sarah.
    fish_house = Int('fish_house')
    solver.add(Or([And(fish_house == h, pet_vars[h] == pets.index("fish")) for h in houses]))
    solver.add(Or([And(fish_house == h, mother_vars[h] == mothers.index("Sarah")) for h in houses]))

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