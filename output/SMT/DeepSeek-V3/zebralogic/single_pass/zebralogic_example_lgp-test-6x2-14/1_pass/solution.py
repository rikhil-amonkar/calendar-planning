from z3 import *

def solve_scheduling_problem():
    # Initialize the solver
    solver = Solver()

    # Define the houses
    houses = [1, 2, 3, 4, 5, 6]

    # Define the names and cigars
    names = ["Carol", "Peter", "Eric", "Arnold", "Alice", "Bob"]
    cigars = ["blends", "yellow monster", "pall mall", "blue master", "dunhill", "prince"]

    # Create variables for each house's name and cigar
    name_vars = [Int(f"name_{i}") for i in houses]
    cigar_vars = [Int(f"cigar_{i}") for i in houses]

    # Add constraints that each name and cigar is unique and within their respective domains
    for var in name_vars:
        solver.add(Or([var == names.index(name) for name in names]))
    solver.add(Distinct(name_vars))

    for var in cigar_vars:
        solver.add(Or([var == cigars.index(cigar) for cigar in cigars]))
    solver.add(Distinct(cigar_vars))

    # Clue 8: Peter is in the first house.
    solver.add(name_vars[0] == names.index("Peter"))

    # Clue 6: Eric is in the sixth house.
    solver.add(name_vars[5] == names.index("Eric"))

    # Clue 9: Bob is in the third house.
    solver.add(name_vars[2] == names.index("Bob"))

    # Clue 5: The person partial to Pall Mall is in the third house.
    solver.add(cigar_vars[2] == cigars.index("pall mall"))

    # Clue 2: The person who smokes Blue Master is in the fifth house.
    solver.add(cigar_vars[4] == cigars.index("blue master"))

    # Clue 7: Carol and Eric are next to each other.
    # Since Eric is in house 6, Carol must be in house 5.
    solver.add(name_vars[4] == names.index("Carol"))

    # Clue 1: Arnold is somewhere to the left of the person who smokes blends.
    # Find the house where blends is smoked and ensure Arnold is to its left.
    blends_index = cigars.index("blends")
    for i in houses:
        solver.add(Implies(cigar_vars[i-1] == blends_index, 
                          Or([name_vars[j-1] == names.index("Arnold") for j in range(1, i)])))

    # Clue 3: Arnold is somewhere to the left of the Prince smoker.
    prince_index = cigars.index("prince")
    for i in houses:
        solver.add(Implies(cigar_vars[i-1] == prince_index, 
                          Or([name_vars[j-1] == names.index("Arnold") for j in range(1, i)])))

    # Clue 4: There is one house between the person who smokes Yellow Monster and the person who smokes blends.
    yellow_monster_index = cigars.index("yellow monster")
    for i in houses:
        for j in houses:
            if abs(i - j) == 2:  # One house between means positions differ by 2
                solver.add(Implies(cigar_vars[i-1] == yellow_monster_index, 
                            cigar_vars[j-1] == blends_index))
                solver.add(Implies(cigar_vars[j-1] == blends_index, 
                            cigar_vars[i-1] == yellow_monster_index))

    # Solve the model
    if solver.check() == sat:
        model = solver.model()
        
        # Prepare the solution
        solution = {
            "solution": {
                "header": ["House", "Name", "Cigar"],
                "rows": []
            }
        }
        
        for house in houses:
            name_index = model.evaluate(name_vars[house-1]).as_long()
            cigar_index = model.evaluate(cigar_vars[house-1]).as_long()
            solution["solution"]["rows"].append([
                str(house),
                names[name_index],
                cigars[cigar_index]
            ])
        
        return solution
    else:
        return {"solution": {"header": ["House", "Name", "Cigar"], "rows": []}}

# Output the solution in JSON format
import json
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))