#!/usr/bin/env python
from z3 import *
import json

def main():
    solver = Solver()
    num_houses = 6

    # Attribute mappings.
    names_map   = {"Arnold": 0, "Peter": 1, "Bob": 2, "Eric": 3, "Carol": 4, "Alice": 5}
    animals_map = {"horse": 0, "rabbit": 1, "fish": 2, "cat": 3, "bird": 4, "dog": 5}
    occ_map     = {"engineer": 0, "nurse": 1, "lawyer": 2, "teacher": 3, "artist": 4, "doctor": 5}
    sports_map  = {"basketball": 0, "volleyball": 1, "soccer": 2, "tennis": 3, "baseball": 4, "swimming": 5}
    heights_map = {"average": 0, "tall": 1, "short": 2, "very short": 3, "very tall": 4, "super tall": 5}

    # Inverse mappings for printing.
    inv_names   = {v: k for k, v in names_map.items()}
    inv_animals = {v: k for k, v in animals_map.items()}
    inv_occ     = {v: k for k, v in occ_map.items()}
    inv_sports  = {v: k for k, v in sports_map.items()}
    inv_heights = {v: k for k, v in heights_map.items()}

    # Create Z3 variables for each house and each attribute.
    names       = [Int(f"name_{i}")       for i in range(num_houses)]
    animals     = [Int(f"animal_{i}")     for i in range(num_houses)]
    occupations = [Int(f"occupation_{i}") for i in range(num_houses)]
    sports      = [Int(f"sport_{i}")      for i in range(num_houses)]
    heights     = [Int(f"height_{i}")     for i in range(num_houses)]

    # Each variable must be in 0..5 and each attribute is unique.
    for i in range(num_houses):
        solver.add(And(names[i] >= 0, names[i] <= 5))
        solver.add(And(animals[i] >= 0, animals[i] <= 5))
        solver.add(And(occupations[i] >= 0, occupations[i] <= 5))
        solver.add(And(sports[i] >= 0, sports[i] <= 5))
        solver.add(And(heights[i] >= 0, heights[i] <= 5))
    solver.add(Distinct(names))
    solver.add(Distinct(animals))
    solver.add(Distinct(occupations))
    solver.add(Distinct(sports))
    solver.add(Distinct(heights))

    # Clue 1: The person who is an engineer is the dog owner.
    for i in range(num_houses):
        solver.add(Implies(occupations[i] == occ_map["engineer"], animals[i] == animals_map["dog"]))
        solver.add(Implies(animals[i] == animals_map["dog"], occupations[i] == occ_map["engineer"]))

    # Clue 2: The person who has an average height is somewhere to the left of the person who is short.
    for i in range(num_houses):
        for j in range(num_houses):
            solver.add(Implies(And(heights[i] == heights_map["average"], heights[j] == heights_map["short"]), i < j))

    # Clue 3: The person who has an average height is directly left of the rabbit owner.
    for i in range(num_houses):
        if i < num_houses - 1:
            solver.add(Implies(heights[i] == heights_map["average"], animals[i+1] == animals_map["rabbit"]))
        else:
            solver.add(heights[i] != heights_map["average"])

    # Clue 4: The person who is tall is somewhere to the left of the person who is very short.
    for i in range(num_houses):
        for j in range(num_houses):
            solver.add(Implies(And(heights[i] == heights_map["tall"], heights[j] == heights_map["very short"]), i < j))

    # Clue 5: Arnold is the cat lover.
    for i in range(num_houses):
        solver.add(Implies(names[i] == names_map["Arnold"], animals[i] == animals_map["cat"]))
        solver.add(Implies(animals[i] == animals_map["cat"], names[i] == names_map["Arnold"]))

    # Clue 6: The person who keeps horses is the person who is a teacher.
    for i in range(num_houses):
        solver.add(Implies(animals[i] == animals_map["horse"], occupations[i] == occ_map["teacher"]))
        solver.add(Implies(occupations[i] == occ_map["teacher"], animals[i] == animals_map["horse"]))

    # Clue 7: Carol is the person who loves soccer.
    for i in range(num_houses):
        solver.add(Implies(names[i] == names_map["Carol"], sports[i] == sports_map["soccer"]))
        solver.add(Implies(sports[i] == sports_map["soccer"], names[i] == names_map["Carol"]))

    # Clue 8: The person who is tall is the person who loves volleyball.
    for i in range(num_houses):
        solver.add(Implies(heights[i] == heights_map["tall"], sports[i] == sports_map["volleyball"]))
        solver.add(Implies(sports[i] == sports_map["volleyball"], heights[i] == heights_map["tall"]))

    # Clue 9: The person who is a lawyer is in the fifth house.
    solver.add(occupations[4] == occ_map["lawyer"])

    # Clue 10: The person who loves tennis is the person who is a teacher.
    for i in range(num_houses):
        solver.add(Implies(sports[i] == sports_map["tennis"], occupations[i] == occ_map["teacher"]))
        solver.add(Implies(occupations[i] == occ_map["teacher"], sports[i] == sports_map["tennis"]))

    # Clue 11: The person who has an average height is the person who loves swimming.
    for i in range(num_houses):
        solver.add(Implies(heights[i] == heights_map["average"], sports[i] == sports_map["swimming"]))
        solver.add(Implies(sports[i] == sports_map["swimming"], heights[i] == heights_map["average"]))

    # Clue 12: The person who loves baseball is directly left of the person who is an engineer.
    for i in range(num_houses):
        if i < num_houses - 1:
            solver.add(Implies(sports[i] == sports_map["baseball"], occupations[i+1] == occ_map["engineer"]))
        else:
            solver.add(sports[i] != sports_map["baseball"])

    # Clue 13: Peter is the person who is a nurse.
    for i in range(num_houses):
        solver.add(Implies(names[i] == names_map["Peter"], occupations[i] == occ_map["nurse"]))
        solver.add(Implies(occupations[i] == occ_map["nurse"], names[i] == names_map["Peter"]))

    # Clue 14: Bob is somewhere to the right of the person who is an artist.
    solver.add(names[0] != names_map["Bob"])
    for i in range(1, num_houses):
        solver.add(Implies(names[i] == names_map["Bob"], 
                           Or([occupations[j] == occ_map["artist"] for j in range(i)])))

    # Clue 15: The person who is a teacher is directly left of the person who loves soccer.
    for i in range(num_houses - 1):
        solver.add(Implies(occupations[i] == occ_map["teacher"], sports[i+1] == sports_map["soccer"]))

    # Clue 16: The rabbit owner is Alice.
    for i in range(num_houses):
        solver.add(Implies(animals[i] == animals_map["rabbit"], names[i] == names_map["Alice"]))
        solver.add(Implies(names[i] == names_map["Alice"], animals[i] == animals_map["rabbit"]))

    # Clue 17: The fish enthusiast is Carol.
    for i in range(num_houses):
        solver.add(Implies(animals[i] == animals_map["fish"], names[i] == names_map["Carol"]))
        solver.add(Implies(names[i] == names_map["Carol"], animals[i] == animals_map["fish"]))

    # Clue 18: The person who loves baseball is in the first house.
    solver.add(sports[0] == sports_map["baseball"])

    # Clue 19: The cat lover is somewhere to the right of the person who is very short.
    for i in range(num_houses):
        solver.add(Implies(animals[i] == animals_map["cat"],
                           Or([heights[j] == heights_map["very short"] for j in range(i)])))

    # Clue 20: The person who is super tall is in the fifth house.
    solver.add(heights[4] == heights_map["super tall"])

    if solver.check() == sat:
        model = solver.model()
        rows = []
        for i in range(num_houses):
            house_number = str(i + 1)
            name_val = inv_names[model.evaluate(names[i]).as_long()]
            animal_val = inv_animals[model.evaluate(animals[i]).as_long()]
            occ_val = inv_occ[model.evaluate(occupations[i]).as_long()]
            sport_val = inv_sports[model.evaluate(sports[i]).as_long()]
            height_val = inv_heights[model.evaluate(heights[i]).as_long()]
            rows.append([house_number, name_val, animal_val, occ_val, sport_val, height_val])
        solution = {
            "solution": {
                "header": ["House", "Name", "Animal", "Occupation", "FavoriteSport", "Height"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        # In case no solution is found.
        solution = {
            "solution": {
                "header": ["House", "Name", "Animal", "Occupation", "FavoriteSport", "Height"],
                "rows": []
            }
        }
        print(json.dumps(solution, indent=2))

if __name__ == "__main__":
    main()