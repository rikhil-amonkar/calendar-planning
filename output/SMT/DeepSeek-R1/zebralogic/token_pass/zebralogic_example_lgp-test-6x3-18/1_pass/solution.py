import z3
import json

def main():
    # Create a solver instance
    solver = z3.Solver()

    # Define the number of houses
    n_houses = 6

    # Create Enum sorts for attributes
    Name = z3.EnumSort('Name', ['Arnold', 'Eric', 'Bob', 'Alice', 'Carol', 'Peter'])
    Mother = z3.EnumSort('Mother', ['Sarah', 'Holly', 'Janelle', 'Aniya', 'Penny', 'Kailyn'])
    Pet = z3.EnumSort('Pet', ['hamster', 'dog', 'bird', 'cat', 'fish', 'rabbit'])

    # Create arrays for each attribute per house
    names = [z3.Const(f'name_{i}', Name) for i in range(n_houses)]
    mothers = [z3.Const(f'mother_{i}', Mother) for i in range(n_houses)]
    pets = [z3.Const(f'pet_{i}', Pet) for i in range(n_houses)]

    # Each attribute must have distinct values across houses
    solver.add(z3.Distinct(names))
    solver.add(z3.Distinct(mothers))
    solver.add(z3.Distinct(pets))

    # Helper functions for positional constraints
    def left_of(a, b):
        return a < b

    def directly_left_of(a, b):
        return a + 1 == b

    def two_houses_between(a, b):
        return z3.Or(a + 3 == b, b + 3 == a)

    def one_house_between(a, b):
        return z3.Or(a + 2 == b, b + 2 == a)

    # Create mappings from attribute values to their constants
    name_vals = {str(name): name for name in Name.__getattr__}
    mother_vals = {str(mother): mother for mother in Mother.__getattr__}
    pet_vals = {str(pet): pet for pet in Pet.__getattr__}

    # Add constraints from clues
    # Clue 1: Bob is not in the second house (index 1)
    solver.add(names[1] != name_vals['Bob'])

    # Clue 2: Two houses between cat and rabbit
    cat_index = z3.Int('cat_index')
    rabbit_index = z3.Int('rabbit_index')
    solver.add(cat_index >= 0, cat_index < n_houses)
    solver.add(rabbit_index >= 0, rabbit_index < n_houses)
    for i in range(n_houses):
        solver.add(z3.Implies(pets[i] == pet_vals['cat'], cat_index == i))
        solver.add(z3.Implies(pets[i] == pet_vals['rabbit'], rabbit_index == i))
    solver.add(two_houses_between(cat_index, rabbit_index))

    # Clue 3: Cat directly left of Holly mother
    holly_index = z3.Int('holly_index')
    solver.add(holly_index >= 0, holly_index < n_houses)
    for i in range(n_houses):
        solver.add(z3.Implies(mothers[i] == mother_vals['Holly'], holly_index == i))
    solver.add(directly_left_of(cat_index, holly_index))

    # Clue 4: Hamster directly left of rabbit
    hamster_index = z3.Int('hamster_index')
    solver.add(hamster_index >= 0, hamster_index < n_houses)
    for i in range(n_houses):
        solver.add(z3.Implies(pets[i] == pet_vals['hamster'], hamster_index == i))
    solver.add(directly_left_of(hamster_index, rabbit_index))

    # Clue 5: Rabbit owner is Eric
    for i in range(n_houses):
        solver.add(z3.Implies(pets[i] == pet_vals['rabbit'], names[i] == name_vals['Eric']))

    # Clue 6: One house between dog and cat
    dog_index = z3.Int('dog_index')
    solver.add(dog_index >= 0, dog_index < n_houses)
    for i in range(n_houses):
        solver.add(z3.Implies(pets[i] == pet_vals['dog'], dog_index == i))
    solver.add(one_house_between(dog_index, cat_index))

    # Clue 7: Cat owner has mother Janelle
    for i in range(n_houses):
        solver.add(z3.Implies(pets[i] == pet_vals['cat'], mothers[i] == mother_vals['Janelle']))

    # Clue 8: Alice directly left of Carol
    alice_index = z3.Int('alice_index')
    carol_index = z3.Int('carol_index')
    solver.add(alice_index >= 0, alice_index < n_houses)
    solver.add(carol_index >= 0, carol_index < n_houses)
    for i in range(n_houses):
        solver.add(z3.Implies(names[i] == name_vals['Alice'], alice_index == i))
        solver.add(z3.Implies(names[i] == name_vals['Carol'], carol_index == i))
    solver.add(directly_left_of(alice_index, carol_index))

    # Clue 9: Carol has mother Aniya
    for i in range(n_houses):
        solver.add(z3.Implies(names[i] == name_vals['Carol'], mothers[i] == mother_vals['Aniya']))

    # Clue 10: Arnold has cat
    for i in range(n_houses):
        solver.add(z3.Implies(names[i] == name_vals['Arnold'], pets[i] == pet_vals['cat']))

    # Clue 11: Kailyn mother has rabbit
    for i in range(n_houses):
        solver.add(z3.Implies(mothers[i] == mother_vals['Kailyn'], pets[i] == pet_vals['rabbit']))

    # Clue 12: Fish owner has mother Sarah
    for i in range(n_houses):
        solver.add(z3.Implies(pets[i] == pet_vals['fish'], mothers[i] == mother_vals['Sarah']))

    # Check satisfiability
    if solver.check() != z3.sat:
        print(json.dumps({"solution": {"header": ["House", "Name", "Mother", "Pet"], "rows": []}}))
        return

    model = solver.model()

    # Prepare results
    header = ["House", "Name", "Mother", "Pet"]
    rows = []
    for i in range(n_houses):
        name_val = model.eval(names[i])
        mother_val = model.eval(mothers[i])
        pet_val = model.eval(pets[i])
        rows.append([str(i+1), str(name_val), str(mother_val), str(pet_val)])

    # Output as JSON
    solution = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(solution))

if __name__ == '__main__':
    main()