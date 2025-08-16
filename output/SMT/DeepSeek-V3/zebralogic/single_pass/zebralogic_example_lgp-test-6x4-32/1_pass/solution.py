from z3 import *

def solve_housing_problem():
    # Initialize the solver
    s = Solver()

    # Define the number of houses
    num_houses = 6
    houses = range(1, num_houses + 1)

    # Define the attributes
    names = ["Eric", "Alice", "Arnold", "Carol", "Peter", "Bob"]
    house_styles = ["mediterranean", "modern", "craftsman", "ranch", "colonial", "victorian"]
    music_genres = ["country", "hip hop", "pop", "jazz", "classical", "rock"]
    hobbies = ["cooking", "painting", "photography", "woodworking", "gardening", "knitting"]

    # Create variables for each attribute in each house
    name = {h: String(f"name_{h}") for h in houses}
    style = {h: String(f"style_{h}") for h in houses}
    music = {h: String(f"music_{h}") for h in houses}
    hobby = {h: String(f"hobby_{h}") for h in houses}

    # Add constraints that each attribute is unique within its category
    s.add(Distinct([name[h] for h in houses]))
    s.add(Distinct([style[h] for h in houses]))
    s.add(Distinct([music[h] for h in houses]))
    s.add(Distinct([hobby[h] for h in houses]))

    # Each attribute must be one of the allowed values
    for h in houses:
        s.add(Or([name[h] == n for n in names]))
        s.add(Or([style[h] == hs for hs in house_styles]))
        s.add(Or([music[h] == mg for mg in music_genres]))
        s.add(Or([hobby[h] == hb for hb in hobbies]))

    # Add the clues as constraints
    # Clue 1: The person who loves rock music is in the fifth house.
    s.add(music[5] == "rock")

    # Clue 2: The person who loves classical music and the woodworking hobbyist are next to each other.
    for h in houses:
        if h < num_houses:
            s.add(Or(
                And(music[h] == "classical", hobby[h+1] == "woodworking"),
                And(music[h+1] == "classical", hobby[h] == "woodworking")
            ))

    # Clue 3: The person in a Mediterranean-style villa is the person who loves hip-hop music.
    for h in houses:
        s.add(Implies(style[h] == "mediterranean", music[h] == "hip hop"))

    # Clue 4: There are two houses between Arnold and the person residing in a Victorian house.
    # Find Arnold's house and the Victorian house
    arnold_house = None
    victorian_house = None
    for h in houses:
        s.add(Implies(name[h] == "Arnold", arnold_house == h))
        s.add(Implies(style[h] == "victorian", victorian_house == h))
    s.add(Or(
        And(arnold_house == 1, victorian_house == 4),
        And(arnold_house == 2, victorian_house == 5),
        And(arnold_house == 3, victorian_house == 6)
    ))

    # Clue 5: The person who loves jazz music is directly left of Eric.
    for h in houses:
        if h < num_houses:
            s.add(Implies(music[h] == "jazz", name[h+1] == "Eric"))

    # Clue 6: The person who loves hip-hop music is somewhere to the left of the person who enjoys knitting.
    # Find hip-hop house and knitting house
    hip_hop_house = None
    knitting_house = None
    for h in houses:
        s.add(Implies(music[h] == "hip hop", hip_hop_house == h))
        s.add(Implies(hobby[h] == "knitting", knitting_house == h))
    s.add(hip_hop_house < knitting_house)

    # Clue 7: Carol is the person who loves hip-hop music.
    for h in houses:
        s.add(Implies(name[h] == "Carol", music[h] == "hip hop"))
        s.add(Implies(music[h] == "hip hop", name[h] == "Carol"))

    # Clue 8: The person in a Craftsman-style house is Arnold.
    for h in houses:
        s.add(Implies(style[h] == "craftsman", name[h] == "Arnold"))
        s.add(Implies(name[h] == "Arnold", style[h] == "craftsman"))

    # Clue 9: The person in a ranch-style home is Eric.
    for h in houses:
        s.add(Implies(style[h] == "ranch", name[h] == "Eric"))
        s.add(Implies(name[h] == "Eric", style[h] == "ranch"))

    # Clue 10: The woodworking hobbyist is the person residing in a Victorian house.
    for h in houses:
        s.add(Implies(hobby[h] == "woodworking", style[h] == "victorian"))
        s.add(Implies(style[h] == "victorian", hobby[h] == "woodworking"))

    # Clue 11: The person who loves country music is in the first house.
    s.add(music[1] == "country")

    # Clue 12: There is one house between the person who paints as a hobby and the person living in a colonial-style house.
    for h in houses:
        if h + 2 <= num_houses:
            s.add(Implies(hobby[h] == "painting", style[h+2] == "colonial"))
        if h - 2 >= 1:
            s.add(Implies(style[h] == "colonial", hobby[h-2] == "painting"))

    # Clue 13: Alice is the photography enthusiast.
    for h in houses:
        s.add(Implies(name[h] == "Alice", hobby[h] == "photography"))
        s.add(Implies(hobby[h] == "photography", name[h] == "Alice"))

    # Clue 14: The person who enjoys gardening is Eric.
    for h in houses:
        s.add(Implies(name[h] == "Eric", hobby[h] == "gardening"))
        s.add(Implies(hobby[h] == "gardening", name[h] == "Eric"))

    # Clue 15: Bob is in the third house.
    s.add(name[3] == "Bob")

    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        # Prepare the solution
        solution = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "MusicGenre", "Hobby"],
                "rows": []
            }
        }
        for h in houses:
            row = [
                str(h),
                model.eval(name[h]).as_string(),
                model.eval(style[h]).as_string(),
                model.eval(music[h]).as_string(),
                model.eval(hobby[h]).as_string()
            ]
            solution["solution"]["rows"].append(row)
        return solution
    else:
        return {"error": "No solution found"}

# Print the solution in JSON format
import json
print(json.dumps(solve_housing_problem(), indent=2))