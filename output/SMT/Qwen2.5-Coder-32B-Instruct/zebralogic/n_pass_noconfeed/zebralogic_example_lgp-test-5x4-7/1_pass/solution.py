from z3 import *

def solve_puzzle():
    # Define the houses
    houses = [Int(f"house_{i}") for i in range(1, 6)]

    # Define the domains for each characteristic
    names = ["Alice", "Peter", "Bob", "Eric", "Arnold"]
    smoothies = ["lime", "dragonfruit", "desert", "watermelon", "cherry"]
    animals = ["horse", "dog", "bird", "fish", "cat"]
    nationalities = ["german", "swede", "norwegian", "brit", "dane"]

    # Create dictionaries to map each characteristic to a variable
    name_vars = {name: Int(name) for name in names}
    smoothie_vars = {smoothie: Int(smoothie) for smoothie in smoothies}
    animal_vars = {animal: Int(animal) for animal in animals}
    nationality_vars = {nationality: Int(nationality) for nationality in nationalities}

    # Create a solver instance
    solver = Solver()

    # Add constraints for each characteristic to be unique and in the range of houses
    for var_dict in [name_vars, smoothie_vars, animal_vars, nationality_vars]:
        solver.add(Distinct(var_dict.values()))
        for var in var_dict.values():
            solver.add(And(var >= 1, var <= 5))

    # Add specific clues as constraints
    solver.add(name_vars["Norwegian"] == 1)  # The Norwegian is Alice.
    solver.add(nationality_vars["swede"] == name_vars["Alice"])  # The Swedish person is directly left of the dog owner.
    solver.add(animal_vars["dog"] == nationality_vars["swede"] + 1)
    solver.add(animal_vars["dog"] - nationality_vars["brit"] == 2)  # Two houses between the dog owner and the British person.
    solver.add(animal_vars["horse"] == 3)  # The Dane is the person who keeps horses.
    solver.add(nationality_vars["dane"] == animal_vars["horse"])
    solver.add(animal_vars["bird"] > animal_vars["cat"])  # The bird keeper is somewhere to the right of the cat lover.
    solver.add(animal_vars["cat"] == name_vars["Eric"])  # Eric is the cat lover.
    solver.add(animal_vars["bird"] == name_vars["Bob"])  # Bob is the bird keeper.
    solver.add(smoothie_vars["cherry"] == name_vars["Peter"] - 1)  # The person who likes Cherry smoothies is directly left of Peter.
    solver.add(smoothie_vars["watermelon"] == animal_vars["bird"])  # The bird keeper is the Watermelon smoothie lover.
    solver.add(smoothie_vars["desert"] == animal_vars["dog"])  # The Desert smoothie lover is the dog owner.
    solver.add(smoothie_vars["lime"] == animal_vars["dog"] + 1)  # The dog owner is directly left of the person who drinks Lime smoothies.

    # Check if the constraints are satisfiable
    if solver.check() == sat:
        model = solver.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "Animal", "Nationality"],
                "rows": []
            }
        }

        # Create a mapping from house number to each characteristic
        house_to_name = {model.evaluate(name_vars[name]).as_long(): name for name in names}
        house_to_smoothie = {model.evaluate(smoothie_vars[smoothie]).as_long(): smoothie for smoothie in smoothies}
        house_to_animal = {model.evaluate(animal_vars[animal]).as_long(): animal for animal in animals}
        house_to_nationality = {model.evaluate(nationality_vars[nationality]).as_long(): nationality for nationality in nationalities}

        # Populate the solution rows
        for house in range(1, 6):
            solution["solution"]["rows"].append([
                str(house),
                house_to_name[house],
                house_to_smoothie[house],
                house_to_animal[house],
                house_to_nationality[house]
            ])

        return solution
    else:
        return None

# Solve the puzzle and print the solution in JSON format
import json
solution = solve_puzzle()
if solution:
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")