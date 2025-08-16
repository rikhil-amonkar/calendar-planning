from z3 import *

def solve_puzzle():
    solver = Solver()

    # Create variables for each house (1-5)
    name = [Int('name_%d' % (i+1)) for i in range(5)]
    flower = [Int('flower_%d' % (i+1)) for i in range(5)]
    animal = [Int('animal_%d' % (i+1)) for i in range(5)]

    # All variables are between 0 and 4
    for i in range(5):
        solver.add(And(0 <= name[i], name[i] <= 4))
        solver.add(And(0 <= flower[i], flower[i] <= 4))
        solver.add(And(0 <= animal[i], animal[i] <= 4))

    # All distinct
    solver.add(Distinct(name))
    solver.add(Distinct(flower))
    solver.add(Distinct(animal))

    # Clue 1: Alice is in house 2 (index 1)
    solver.add(name[1] == 0)

    # Clue 8: house 3 (index 2) has animal horse (1) and name Eric (1)
    solver.add(animal[2] == 1, name[2] == 1)

    # Clue 2: lilies (flower 2) implies bird (animal 3)
    for i in range(5):
        solver.add(Implies(flower[i] == 2, animal[i] == 3))

    # Clue 3: Peter (name 4) is to the right of tulips (flower 0)
    for i in range(4):  # original houses 1-4 (indices 0-3)
        or_expr = Or([name[j] == 4 for j in range(i+1, 5)])
        solver.add(Implies(flower[i] == 0, or_expr))
    solver.add(flower[4] != 0)  # original house 5 can't have tulips

    # Clue 4: fish (animal 4) implies daffodils (flower 3)
    for i in range(5):
        solver.add(Implies(animal[i] == 4, flower[i] == 3))

    # Clue 6: |dog_house - bob_house| == 3
    dog_house = Int('dog_house')
    bob_house = Int('bob_house')
    for i in range(5):
        # dog_house constraints
        solver.add(Implies(animal[i] == 0, dog_house == (i+1)))
        solver.add(Implies(dog_house == (i+1), animal[i] == 0))
        # bob_house constraints
        solver.add(Implies(name[i] == 3, bob_house == (i+1)))
        solver.add(Implies(bob_house == (i+1), name[i] == 3))
    solver.add(Abs(dog_house - bob_house) == 3)

    # Clue 7: fish_house +1 = bob_house
    fish_house = Int('fish_house')
    for i in range(5):
        solver.add(Implies(animal[i] == 4, fish_house == (i+1)))
        solver.add(Implies(fish_house == (i+1), animal[i] == 4))
    solver.add(bob_house == fish_house + 1)

    # Clue 9: carnations (flower 4) is directly left of tulips (flower 0)
    for i in range(4):  # original houses 1-4 (indices 0-3)
        solver.add(Implies(flower[i] == 4, flower[i+1] == 0))

    # Clue 10: animal_1 != cat (animal 2)
    solver.add(animal[0] != 2)

    if solver.check() == sat:
        model = solver.model()
        # Now extract the values for each house
        solution = []
        for i in range(5):
            house_num = i + 1
            n = model[name[i]].as_long()
            f = model[flower[i]].as_long()
            a = model[animal[i]].as_long()
            solution.append([str(house_num), n, f, a])
        # Now map the integers to the actual names, flowers, animals
        name_map = {0: "Alice", 1: "Eric", 2: "Arnold", 3: "Bob", 4: "Peter"}
        flower_map = {0: "tulips", 1: "roses", 2: "lilies", 3: "daffodils", 4: "carnations"}
        animal_map = {0: "dog", 1: "horse", 2: "cat", 3: "bird", 4: "fish"}
        # Convert the solution
        rows = []
        for entry in solution:
            house = entry[0]
            n = name_map[entry[1]]
            f = flower_map[entry[2]]
            a = animal_map[entry[3]]
            rows.append([house, n, f, a])
        # Output JSON
        import json
        json_output = {
            "solution": {
                "header": ["House", "Name", "Flower", "Animal"],
                "rows": rows
            }
        }
        return json_output
    else:
        return {"error": "No solution found."}

# Run the solver and print the result
import json
result = solve_puzzle()
print(json.dumps(result, indent=2))