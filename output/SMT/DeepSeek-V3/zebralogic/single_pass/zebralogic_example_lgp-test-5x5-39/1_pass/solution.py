import json
from z3 import *

def solve_puzzle():
    # Initialize the solver
    s = Solver()

    # Define the houses
    houses = [1, 2, 3, 4, 5]

    # Define the attributes
    names = ["Alice", "Eric", "Bob", "Peter", "Arnold"]
    months = ["mar", "april", "sept", "feb", "jan"]
    mothers = ["Holly", "Janelle", "Kailyn", "Penny", "Aniya"]
    occupations = ["engineer", "doctor", "lawyer", "artist", "teacher"]
    hair_colors = ["red", "blonde", "black", "gray", "brown"]

    # Create variables for each attribute in each house
    name = {h: String(f"name_{h}") for h in houses}
    month = {h: String(f"month_{h}") for h in houses}
    mother = {h: String(f"mother_{h}") for h in houses}
    occupation = {h: String(f"occupation_{h}") for h in houses}
    hair_color = {h: String(f"hair_color_{h}") for h in houses}

    # Add constraints that each attribute is unique within its category
    for h in houses:
        s.add(Or([name[h] == n for n in names]))
        s.add(Or([month[h] == m for m in months]))
        s.add(Or([mother[h] == m for m in mothers]))
        s.add(Or([occupation[h] == o for o in occupations]))
        s.add(Or([hair_color[h] == hc for hc in hair_colors]))

    for attr in [name, month, mother, occupation, hair_color]:
        for h1 in houses:
            for h2 in houses:
                if h1 < h2:
                    s.add(attr[h1] != attr[h2])

    # Add the clues as constraints
    # Clue 1: The person whose birthday is in March is in the fifth house.
    s.add(month[5] == "mar")

    # Clue 2: The person whose birthday is in February is in the first house.
    s.add(month[1] == "feb")

    # Clue 3: The person who is a doctor is Eric.
    for h in houses:
        s.add(Implies(occupation[h] == "doctor", name[h] == "Eric"))

    # Clue 4: The person whose mother's name is Janelle is in the third house.
    s.add(mother[3] == "Janelle")

    # Clue 5: The person who is an artist is the person who has brown hair.
    for h in houses:
        s.add(Implies(occupation[h] == "artist", hair_color[h] == "brown"))

    # Clue 6: The person who is an artist is in the fourth house.
    s.add(occupation[4] == "artist")

    # Clue 7: The person whose mother's name is Penny is somewhere to the left of the person who has black hair.
    # This means that the house with mother Penny has a lower number than the house with black hair.
    for h_penny in houses:
        for h_black in houses:
            if h_penny < h_black:
                s.add(Implies(mother[h_penny] == "Penny", hair_color[h_black] == "black"))

    # Clue 8: Peter is the person who has black hair.
    for h in houses:
        s.add(Implies(name[h] == "Peter", hair_color[h] == "black"))

    # Clue 9: The person who has gray hair is the person who is a teacher.
    for h in houses:
        s.add(Implies(hair_color[h] == "gray", occupation[h] == "teacher"))

    # Clue 10: Alice is the person whose mother's name is Kailyn.
    for h in houses:
        s.add(Implies(name[h] == "Alice", mother[h] == "Kailyn"))

    # Clue 11: Arnold is somewhere to the right of the person whose birthday is in September.
    # This means the house with Arnold has a higher number than the house with September birthday.
    for h_sept in houses:
        for h_arnold in houses:
            if h_sept < h_arnold:
                s.add(Implies(month[h_sept] == "sept", name[h_arnold] == "Arnold"))

    # Clue 12: The person who has brown hair is the person whose birthday is in January.
    for h in houses:
        s.add(Implies(hair_color[h] == "brown", month[h] == "jan"))

    # Clue 13: Arnold is the person who has blonde hair.
    for h in houses:
        s.add(Implies(name[h] == "Arnold", hair_color[h] == "blonde"))

    # Clue 14: The person whose mother's name is Holly is the person who has black hair.
    for h in houses:
        s.add(Implies(mother[h] == "Holly", hair_color[h] == "black"))

    # Clue 15: Peter is the person who is a lawyer.
    for h in houses:
        s.add(Implies(name[h] == "Peter", occupation[h] == "lawyer"))

    # Clue 16: The person whose birthday is in September is somewhere to the left of the person whose mother's name is Kailyn.
    # This means the house with September birthday has a lower number than the house with mother Kailyn.
    for h_sept in houses:
        for h_kailyn in houses:
            if h_sept < h_kailyn:
                s.add(Implies(month[h_sept] == "sept", mother[h_kailyn] == "Kailyn"))

    # Clue 17: Alice is the person who has gray hair.
    for h in houses:
        s.add(Implies(name[h] == "Alice", hair_color[h] == "gray"))

    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "Birthday", "Mother", "Occupation", "HairColor"],
                "rows": []
            }
        }
        for h in sorted(houses):
            row = [
                str(h),
                str(model.eval(name[h])),
                str(model.eval(month[h])),
                str(model.eval(mother[h])),
                str(model.eval(occupation[h])),
                str(model.eval(hair_color[h]))
            ]
            solution["solution"]["rows"].append(row)
        return json.dumps(solution, indent=2)
    else:
        return json.dumps({"error": "No solution found"}, indent=2)

print(solve_puzzle())