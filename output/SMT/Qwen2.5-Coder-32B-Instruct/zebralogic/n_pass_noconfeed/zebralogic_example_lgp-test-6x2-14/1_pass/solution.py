from z3 import *

def solve_puzzle():
    # Define the variables
    names = ["Carol", "Peter", "Eric", "Arnold", "Alice", "Bob"]
    cigars = ["blends", "yellow monster", "pall mall", "blue master", "dunhill", "prince"]
    houses = range(1, 7)

    # Create dictionaries to map names and cigars to their respective house numbers
    name_vars = {name: Int(name) for name in names}
    cigar_vars = {cigar: Int(cigar) for cigar in cigars}

    # Create the solver
    solver = Solver()

    # Add constraints for each name and cigar to be in a unique house
    for var in list(name_vars.values()) + list(cigar_vars.values()):
        solver.add(var >= 1)
        solver.add(var <= 6)

    for i in range(len(names)):
        for j in range(i + 1, len(names)):
            solver.add(name_vars[names[i]] != name_vars[names[j]])
            solver.add(cigar_vars[cigars[i]] != cigar_vars[cigars[j]])

    # Clue 1: Arnold is somewhere to the left of the person who smokes many unique blends.
    solver.add(name_vars["Arnold"] < cigar_vars["blends"])

    # Clue 2: The person who smokes Blue Master is in the fifth house.
    solver.add(cigar_vars["blue master"] == 5)

    # Clue 3: Arnold is somewhere to the left of the Prince smoker.
    solver.add(name_vars["Arnold"] < cigar_vars["prince"])

    # Clue 4: There is one house between the person who smokes Yellow Monster and the person who smokes many unique blends.
    solver.add(Abs(cigar_vars["yellow monster"] - cigar_vars["blends"]) == 2)

    # Clue 5: The person partial to Pall Mall is in the third house.
    solver.add(cigar_vars["pall mall"] == 3)

    # Clue 6: Eric is in the sixth house.
    solver.add(name_vars["Eric"] == 6)

    # Clue 7: Carol and Eric are next to each other.
    solver.add(Abs(name_vars["Carol"] - name_vars["Eric"]) == 1)

    # Clue 8: Peter is in the first house.
    solver.add(name_vars["Peter"] == 1)

    # Clue 9: Bob is in the third house.
    solver.add(name_vars["Bob"] == 3)

    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        solution = []
        for house in houses:
            name = next(name for name, var in name_vars.items() if model.evaluate(var) == house).as_string()[1:-1]
            cigar = next(cigar for cigar, var in cigar_vars.items() if model.evaluate(var) == house).as_string()[1:-1]
            solution.append([str(house), name, cigar])

        return {
            "solution": {
                "header": ["House", "Name", "Cigar"],
                "rows": solution
            }
        }

    else:
        return None

# Output the solution as JSON
import json
print(json.dumps(solve_puzzle(), indent=2))