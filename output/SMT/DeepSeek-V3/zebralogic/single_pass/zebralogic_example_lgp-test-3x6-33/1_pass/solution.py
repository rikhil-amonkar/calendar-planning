from z3 import *

def solve_puzzle():
    # Create solver
    s = Solver()

    # Define the houses
    houses = [1, 2, 3]

    # Define attributes
    names = ["Arnold", "Eric", "Peter"]
    flowers = ["carnations", "lilies", "daffodils"]
    hair_colors = ["black", "brown", "blonde"]
    sports = ["soccer", "basketball", "tennis"]
    house_styles = ["colonial", "ranch", "victorian"]
    pets = ["fish", "dog", "cat"]

    # Create variables for each attribute in each house
    name = {h: String(f"name_{h}") for h in houses}
    flower = {h: String(f"flower_{h}") for h in houses}
    hair_color = {h: String(f"hair_color_{h}") for h in houses}
    favorite_sport = {h: String(f"favorite_sport_{h}") for h in houses}
    house_style = {h: String(f"house_style_{h}") for h in houses}
    pet = {h: String(f"pet_{h}") for h in houses}

    # Add constraints that each attribute is unique within its category
    s.add(Distinct([name[h] for h in houses]))
    s.add(Distinct([flower[h] for h in houses]))
    s.add(Distinct([hair_color[h] for h in houses]))
    s.add(Distinct([favorite_sport[h] for h in houses]))
    s.add(Distinct([house_style[h] for h in houses]))
    s.add(Distinct([pet[h] for h in houses]))

    # Each attribute must be one of the allowed values
    for h in houses:
        s.add(Or([name[h] == n for n in names]))
        s.add(Or([flower[h] == f for f in flowers]))
        s.add(Or([hair_color[h] == hc for hc in hair_colors]))
        s.add(Or([favorite_sport[h] == sp for sp in sports]))
        s.add(Or([house_style[h] == hs for hs in house_styles]))
        s.add(Or([pet[h] == p for p in pets]))

    # Add the clues as constraints
    # Clue 1: The person who has a cat is the person who loves soccer.
    for h in houses:
        s.add(Implies(pet[h] == "cat", favorite_sport[h] == "soccer"))

    # Clue 2: The person who has blonde hair is in the second house.
    s.add(hair_color[2] == "blonde")

    # Clue 3: The person who loves a bouquet of daffodils is the person who has blonde hair.
    s.add(flower[2] == "daffodils")

    # Clue 4: Peter is the person who loves basketball.
    for h in houses:
        s.add(Implies(name[h] == "Peter", favorite_sport[h] == "basketball"))

    # Clue 5: Arnold is directly left of the person in a ranch-style home.
    s.add(Or(
        And(name[1] == "Arnold", house_style[2] == "ranch"),
        And(name[2] == "Arnold", house_style[3] == "ranch")
    ))

    # Clue 6: The person who owns a dog is the person who loves basketball.
    for h in houses:
        s.add(Implies(pet[h] == "dog", favorite_sport[h] == "basketball"))

    # Clue 7: The person who loves a carnations arrangement is directly left of the person who has blonde hair.
    s.add(flower[1] == "carnations")

    # Clue 8: The person who loves soccer is in the third house.
    s.add(favorite_sport[3] == "soccer")

    # Clue 9: Arnold is somewhere to the left of the person who has black hair.
    # This means Arnold is in a house with a lower number than the person with black hair
    s.add(Or(
        And(name[1] == "Arnold", Or(hair_color[2] == "black", hair_color[3] == "black")),
        And(name[2] == "Arnold", hair_color[3] == "black")
    ))

    # Clue 10: The person living in a colonial-style house is in the third house.
    s.add(house_style[3] == "colonial")

    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        
        # Prepare the solution
        solution = {
            "solution": {
                "header": ["House", "Name", "Flower", "HairColor", "FavoriteSport", "HouseStyle", "Pet"],
                "rows": []
            }
        }
        
        # Collect the values for each house
        for h in sorted(houses):
            row = [
                str(h),
                str(m.evaluate(name[h])),
                str(m.evaluate(flower[h])),
                str(m.evaluate(hair_color[h])),
                str(m.evaluate(favorite_sport[h])),
                str(m.evaluate(house_style[h])),
                str(m.evaluate(pet[h]))
            ]
            solution["solution"]["rows"].append(row)
        
        return solution
    else:
        return {"error": "No solution found"}

# Solve the puzzle and print the result
solution = solve_puzzle()
import json
print(json.dumps(solution, indent=2))