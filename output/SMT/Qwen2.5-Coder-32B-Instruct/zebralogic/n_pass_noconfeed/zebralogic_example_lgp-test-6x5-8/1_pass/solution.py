from z3 import *

def solve_puzzle():
    # Define domains
    houses = range(1, 7)
    names = ["Arnold", "Peter", "Bob", "Eric", "Carol", "Alice"]
    animals = ["horse", "rabbit", "fish", "cat", "bird", "dog"]
    occupations = ["engineer", "nurse", "lawyer", "teacher", "artist", "doctor"]
    favorite_sports = ["basketball", "volleyball", "soccer", "tennis", "baseball", "swimming"]
    heights = ["average", "tall", "short", "very short", "very tall", "super tall"]

    # Create solver
    solver = Solver()

    # Declare variables
    name_vars = {h: Int(f'name_{h}') for h in houses}
    animal_vars = {h: Int(f'animal_{h}') for h in houses}
    occupation_vars = {h: Int(f'occupation_{h}') for h in houses}
    sport_vars = {h: Int(f'sport_{h}') for h in houses}
    height_vars = {h: Int(f'height_{h}') for h in houses}

    # Define constraints for unique values
    for h in houses:
        solver.add(name_vars[h] >= 0, name_vars[h] < len(names))
        solver.add(animal_vars[h] >= 0, animal_vars[h] < len(animals))
        solver.add(occupation_vars[h] >= 0, occupation_vars[h] < len(occupations))
        solver.add(sport_vars[h] >= 0, sport_vars[h] < len(favorite_sports))
        solver.add(height_vars[h] >= 0, height_vars[h] < len(heights))

    # All values must be unique across houses
    solver.add(Distinct([name_vars[h] for h in houses]))
    solver.add(Distinct([animal_vars[h] for h in houses]))
    solver.add(Distinct([occupation_vars[h] for h in houses]))
    solver.add(Distinct([sport_vars[h] for h in houses]))
    solver.add(Distinct([height_vars[h] for h in houses]))

    # Clue 1: The person who is an engineer is the dog owner.
    solver.add(And([If(occupation_vars[h] == occupations.index("engineer"), animal_vars[h] == animals.index("dog"), True) for h in houses]))

    # Clue 2: The person who has an average height is somewhere to the left of the person who is short.
    solver.add(Or([And(height_vars[i] == heights.index("average"), height_vars[j] == heights.index("short")) for i in houses for j in houses if i < j]))

    # Clue 3: The person who has an average height is directly left of the rabbit owner.
    solver.add(Or([And(height_vars[h] == heights.index("average"), animal_vars[h + 1] == animals.index("rabbit")) for h in houses if h < 6]))

    # Clue 4: The person who is tall is somewhere to the left of the person who is very short.
    solver.add(Or([And(height_vars[i] == heights.index("tall"), height_vars[j] == heights.index("very short")) for i in houses for j in houses if i < j]))

    # Clue 5: Arnold is the cat lover.
    solver.add(Or([And(name_vars[h] == names.index("Arnold"), animal_vars[h] == animals.index("cat")) for h in houses]))

    # Clue 6: The person who keeps horses is the person who is a teacher.
    solver.add(Or([And(animal_vars[h] == animals.index("horse"), occupation_vars[h] == occupations.index("teacher")) for h in houses]))

    # Clue 7: Carol is the person who loves soccer.
    solver.add(Or([And(name_vars[h] == names.index("Carol"), sport_vars[h] == favorite_sports.index("soccer")) for h in houses]))

    # Clue 8: The person who is tall is the person who loves volleyball.
    solver.add(Or([And(height_vars[h] == heights.index("tall"), sport_vars[h] == favorite_sports.index("volleyball")) for h in houses]))

    # Clue 9: The person who is a lawyer is in the fifth house.
    solver.add(occupation_vars[5] == occupations.index("lawyer"))

    # Clue 10: The person who loves tennis is the person who is a teacher.
    solver.add(Or([And(sport_vars[h] == favorite_sports.index("tennis"), occupation_vars[h] == occupations.index("teacher")) for h in houses]))

    # Clue 11: The person who has an average height is the person who loves swimming.
    solver.add(Or([And(height_vars[h] == heights.index("average"), sport_vars[h] == favorite_sports.index("swimming")) for h in houses]))

    # Clue 12: The person who loves baseball is directly left of the person who is an engineer.
    solver.add(Or([And(sport_vars[h] == favorite_sports.index("baseball"), occupation_vars[h + 1] == occupations.index("engineer")) for h in houses if h < 6]))

    # Clue 13: Peter is the person who is a nurse.
    solver.add(Or([And(name_vars[h] == names.index("Peter"), occupation_vars[h] == occupations.index("nurse")) for h in houses]))

    # Clue 14: Bob is somewhere to the right of the person who is an artist.
    solver.add(Or([And(name_vars[i] == names.index("Bob"), name_vars[j] == names.index("artist")) for i in houses for j in houses if i > j]))

    # Clue 15: The person who is a teacher is directly left of the person who loves soccer.
    solver.add(Or([And(occupation_vars[h] == occupations.index("teacher"), sport_vars[h + 1] == favorite_sports.index("soccer")) for h in houses if h < 6]))

    # Clue 16: The rabbit owner is Alice.
    solver.add(Or([And(animal_vars[h] == animals.index("rabbit"), name_vars[h] == names.index("Alice")) for h in houses]))

    # Clue 17: The fish enthusiast is Carol.
    solver.add(Or([And(animal_vars[h] == animals.index("fish"), name_vars[h] == names.index("Carol")) for h in houses]))

    # Clue 18: The person who loves baseball is in the first house.
    solver.add(sport_vars[1] == favorite_sports.index("baseball"))

    # Clue 19: The cat lover is somewhere to the right of the person who is very short.
    solver.add(Or([And(animal_vars[i] == animals.index("cat"), height_vars[j] == heights.index("very short")) for i in houses for j in houses if i > j]))

    # Clue 20: The person who is super tall is in the fifth house.
    solver.add(height_vars[5] == heights.index("super tall"))

    # Check if the model is satisfiable
    if solver.check() == sat:
        model = solver.model()
        result = {
            "solution": {
                "header": ["House", "Name", "Animal", "Occupation", "FavoriteSport", "Height"],
                "rows": []
            }
        }
        for h in houses:
            name = names[model[name_vars[h]].as_long()]
            animal = animals[model[animal_vars[h]].as_long()]
            occupation = occupations[model[occupation_vars[h]].as_long()]
            sport = favorite_sports[model[sport_vars[h]].as_long()]
            height = heights[model[height_vars[h]].as_long()]
            result["solution"]["rows"].append([str(h), name, animal, occupation, sport, height])
        return result
    else:
        return None

# Solve the puzzle and print the result as JSON
import json
print(json.dumps(solve_puzzle(), indent=2))