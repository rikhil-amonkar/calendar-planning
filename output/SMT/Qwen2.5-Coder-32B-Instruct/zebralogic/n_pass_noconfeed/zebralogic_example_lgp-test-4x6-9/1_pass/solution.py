from z3 import *

def solve_puzzle():
    # Define the domains
    houses = [1, 2, 3, 4]
    names = ["Peter", "Arnold", "Eric", "Alice"]
    flowers = ["daffodils", "carnations", "roses", "lilies"]
    heights = ["very short", "short", "tall", "average"]
    mothers = ["Janelle", "Kailyn", "Holly", "Aniya"]
    occupations = ["engineer", "doctor", "teacher", "artist"]
    sports = ["swimming", "basketball", "tennis", "soccer"]

    # Create Solver
    solver = Solver()

    # Declare variables
    house_name = {h: Int(f"house_{h}_name") for h in houses}
    house_flower = {h: Int(f"house_{h}_flower") for h in houses}
    house_height = {h: Int(f"house_{h}_height") for h in houses}
    house_mother = {h: Int(f"house_{h}_mother") for h in houses}
    house_occupation = {h: Int(f"house_{h}_occupation") for h in houses}
    house_sport = {h: Int(f"house_{h}_sport") for h in houses}

    # Add domain constraints
    for h in houses:
        solver.add(house_name[h] >= 0)
        solver.add(house_name[h] < len(names))
        solver.add(house_flower[h] >= 0)
        solver.add(house_flower[h] < len(flowers))
        solver.add(house_height[h] >= 0)
        solver.add(house_height[h] < len(heights))
        solver.add(house_mother[h] >= 0)
        solver.add(house_mother[h] < len(mothers))
        solver.add(house_occupation[h] >= 0)
        solver.add(house_occupation[h] < len(occupations))
        solver.add(house_sport[h] >= 0)
        solver.add(house_sport[h] < len(sports))

    # All values must be unique across houses
    solver.add(Distinct([house_name[h] for h in houses]))
    solver.add(Distinct([house_flower[h] for h in houses]))
    solver.add(Distinct([house_height[h] for h in houses]))
    solver.add(Distinct([house_mother[h] for h in houses]))
    solver.add(Distinct([house_occupation[h] for h in houses]))
    solver.add(Distinct([house_sport[h] for h in houses]))

    # Clue constraints
    solver.add(house_name[1] == names.index("Peter"))
    solver.add(house_name[1] == occupations.index("doctor"))
    solver.add(house_name[2] == names.index("Arnold"))
    solver.add(house_name[2] == heights.index("tall"))
    solver.add(house_name[2] == flowers.index("lilies"))
    solver.add(house_name[3] != names.index("Arnold"))
    solver.add(house_name[4] == mothers.index("Aniya"))
    solver.add(house_name[4] == names.index("Alice"))
    solver.add(house_sport[1] == sports.index("tennis"))
    solver.add(house_occupation[1] == occupations.index("teacher"))
    solver.add(house_flower[2] == flowers.index("roses"))
    solver.add(house_sport[2] == sports.index("swimming"))
    solver.add(house_height[3] == heights.index("short"))
    solver.add(house_sport[3] == sports.index("soccer"))
    solver.add(house_height[4] == heights.index("average"))
    solver.add(house_sport[4] == sports.index("basketball"))
    solver.add(house_flower[3] == flowers.index("daffodils"))
    solver.add(house_flower[4] == flowers.index("carnations"))
    solver.add(house_mother[2] == mothers.index("Janelle"))
    solver.add(house_mother[4] == mothers.index("Holly"))

    # Additional constraints from clues
    solver.add(Or(house_flower[h] != flowers.index("daffodils") for h in range(1, 4)) | Or(house_occupation[h] != occupations.index("engineer") for h in range(1, 4)))
    solver.add(Or(house_height[h] != heights.index("average") for h in range(1, 4)) | Or(house_mother[h] != mothers.index("Holly") for h in range(1, 4)))

    # Solve the puzzle
    if solver.check() == sat:
        model = solver.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "Flower", "Height", "Mother", "Occupation", "FavoriteSport"],
                "rows": []
            }
        }
        for h in houses:
            name = names[model.eval(house_name[h]).as_long()]
            flower = flowers[model.eval(house_flower[h]).as_long()]
            height = heights[model.eval(house_height[h]).as_long()]
            mother = mothers[model.eval(house_mother[h]).as_long()]
            occupation = occupations[model.eval(house_occupation[h]).as_long()]
            sport = sports[model.eval(house_sport[h]).as_long()]
            solution["solution"]["rows"].append([str(h), name, flower, height, mother, occupation, sport])
        return solution
    else:
        return None

# Output the solution as JSON
import json
print(json.dumps(solve_puzzle(), indent=2))