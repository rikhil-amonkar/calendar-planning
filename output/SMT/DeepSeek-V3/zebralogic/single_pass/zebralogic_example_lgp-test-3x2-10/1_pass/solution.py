from z3 import *

def solve_scheduling_problem():
    # Create a solver instance
    solver = Solver()

    # Define the houses
    houses = [1, 2, 3]

    # Define the names and heights
    names = ["Eric", "Arnold", "Peter"]
    heights = ["very short", "short", "average"]

    # Create variables for each house's name and height
    name_vars = {house: String(f"name_{house}") for house in houses}
    height_vars = {house: String(f"height_{house}") for house in houses}

    # Add constraints that each name and height is unique
    solver.add(Distinct([name_vars[house] for house in houses]))
    solver.add(Distinct([height_vars[house] for house in houses]))

    # Each name and height must be one of the allowed values
    for house in houses:
        solver.add(Or([name_vars[house] == name for name in names]))
        solver.add(Or([height_vars[house] == height for height in heights]))

    # Clue 1: Eric is not in the first house.
    solver.add(name_vars[1] != "Eric")

    # Clue 2: The person who is very short is somewhere to the left of the person who is short.
    # This means the house number of very short is less than the house number of short.
    very_short_house = Int("very_short_house")
    short_house = Int("short_house")
    solver.add(Or([And(height_vars[house] == "very short", very_short_house == house) for house in houses]))
    solver.add(Or([And(height_vars[house] == "short", short_house == house) for house in houses]))
    solver.add(very_short_house < short_house)

    # Clue 3: The person who is very short is Eric.
    # So for the house where height is very short, name is Eric.
    for house in houses:
        solver.add(Implies(height_vars[house] == "very short", name_vars[house] == "Eric"))

    # Clue 4: Arnold is not in the first house.
    solver.add(name_vars[1] != "Arnold")

    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        solution = {"solution": {"header": ["House", "Name", "Height"], "rows": []}}
        for house in sorted(houses):
            name_val = model.eval(name_vars[house]).as_string()
            height_val = model.eval(height_vars[house]).as_string()
            solution["solution"]["rows"].append([str(house), name_val, height_val])
        return solution
    else:
        return {"solution": {"header": ["House", "Name", "Height"], "rows": []}}

# Generate the solution
solution = solve_scheduling_problem()
print(solution)