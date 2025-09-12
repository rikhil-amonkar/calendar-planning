from z3 import *

def solve_puzzle():
    # Define the variables
    names = ['Alice', 'Eric', 'Arnold', 'Bob', 'Peter']
    flowers = ['tulips', 'roses', 'lilies', 'daffodils', 'carnations']
    animals = ['dog', 'horse', 'cat', 'bird', 'fish']
    houses = range(1, 6)

    # Create symbolic variables
    name_vars = {house: Int(f'name_{house}') for house in houses}
    flower_vars = {house: Int(f'flower_{house}') for house in houses}
    animal_vars = {house: Int(f'animal_{house}') for house in houses}

    # Create the solver
    solver = Solver()

    # Add constraints for unique values in each category
    solver.add(Distinct([name_vars[house] for house in houses]))
    solver.add(Distinct([flower_vars[house] for house in houses]))
    solver.add(Distinct([animal_vars[house] for house in houses]))

    # Map indices to names, flowers, and animals
    name_map = {name: i for i, name in enumerate(names)}
    flower_map = {flower: i for i, flower in enumerate(flowers)}
    animal_map = {animal: i for i, animal in enumerate(animals)}

    # Add specific constraints based on the clues
    solver.add(name_vars[2] == name_map['Alice'])  # Clue 1
    for i in houses:
        solver.add(Implies(flower_vars[i] == flower_map['lilies'], animal_vars[i] == animal_map['bird']))  # Clue 2
    for j in range(5):
        if j + 1 < 6:
            solver.add(Implies(name_vars[j + 1] == name_map['Alice'], Or([name_vars[i] == name_map['Peter'] for i in range(j + 1, 6)])))  # Clue 3
    for i in houses:
        solver.add(Implies(animal_vars[i] == animal_map['fish'], flower_vars[i] == flower_map['daffodils']))  # Clue 4
    for i in houses:
        solver.add(Implies(animal_vars[i] == animal_map['horse'], name_vars[i] == name_map['Eric']))  # Clue 5
    for i in houses:
        if i - 3 in houses:
            solver.add(Implies(name_vars[i - 3] == name_map['dog'], name_vars[i] == name_map['Bob']))  # Clue 6 part 1
        if i + 3 in houses:
            solver.add(Implies(name_vars[i + 3] == name_map['dog'], name_vars[i] == name_map['Bob']))  # Clue 6 part 2
    for i in range(1, 5):
        solver.add(Implies(animal_vars[i] == animal_map['fish'], name_vars[i + 1] == name_map['Bob']))  # Clue 7
    for i in range(1, 5):
        solver.add(Implies(name_vars[i] == name_map['Alice'], animal_vars[i + 1] == animal_map['horse']))  # Clue 8
    for i in range(1, 5):
        solver.add(Implies(flower_vars[i] == flower_map['carnations'], flower_vars[i + 1] == flower_map['tulips']))  # Clue 9
    for i in houses:
        solver.add(Implies(animal_vars[i] == animal_map['cat'], name_vars[i] != name_map['Arnold']))  # Clue 10

    # Check if the constraints are satisfiable
    if solver.check() == sat:
        model = solver.model()
        solution = []
        for house in houses:
            name = names[model.evaluate(name_vars[house]).as_long()]
            flower = flowers[model.evaluate(flower_vars[house]).as_long()]
            animal = animals[model.evaluate(animal_vars[house]).as_long()]
            solution.append([str(house), name, flower, animal])
        
        return {
            "solution": {
                "header": ["House", "Name", "Flower", "Animal"],
                "rows": solution
            }
        }
    else:
        return None

# Output the solution as JSON
import json
print(json.dumps(solve_puzzle(), indent=2))