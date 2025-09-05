from z3 import Int, Solver, Or, sat
import json

def main():
    # Create a solver instance
    solver = Solver()
    
    # Define integer variables for houses (domain: 1 to 2).
    Arnold = Int('Arnold')
    Eric = Int('Eric')
    beach = Int('beach')
    mountain = Int('mountain')
    
    # Constraint: Each variable is either 1 or 2.
    solver.add(Or(Arnold == 1, Arnold == 2))
    solver.add(Or(Eric == 1, Eric == 2))
    solver.add(Or(beach == 1, beach == 2))
    solver.add(Or(mountain == 1, mountain == 2))
    
    # Each name is in a different house.
    solver.add(Arnold != Eric)
    
    # Each vacation type is unique.
    solver.add(beach != mountain)
    
    # Clue constraint: "Arnold is somewhere to the right of the person who loves beach vacations."
    # i.e., the house number for Arnold is greater than that for beach.
    solver.add(Arnold > beach)
    
    # Check if the constraints are satisfiable.
    if solver.check() == sat:
        model = solver.model()
        
        # Prepare a mapping for houses 1 and 2.
        houses = {1: {"Name": None, "Vacation": None},
                  2: {"Name": None, "Vacation": None}}
        
        # Assign names based on the model evaluation.
        if model.evaluate(Arnold).as_long() == 1:
            houses[1]["Name"] = "Arnold"
        else:
            houses[2]["Name"] = "Arnold"
        
        if model.evaluate(Eric).as_long() == 1:
            houses[1]["Name"] = "Eric"
        else:
            houses[2]["Name"] = "Eric"
        
        # Assign vacation preferences based on the model evaluation.
        if model.evaluate(beach).as_long() == 1:
            houses[1]["Vacation"] = "beach"
        else:
            houses[2]["Vacation"] = "beach"
        
        if model.evaluate(mountain).as_long() == 1:
            houses[1]["Vacation"] = "mountain"
        else:
            houses[2]["Vacation"] = "mountain"
        
        # Order the results by house number.
        rows = []
        for house_number in sorted(houses.keys()):
            row = [str(house_number), houses[house_number]["Name"], houses[house_number]["Vacation"]]
            rows.append(row)
        
        # Construct the output dictionary as specified.
        output = {
            "solution": {
                "header": ["House", "Name", "Vacation"],
                "rows": rows
            }
        }
        print(json.dumps(output))
    else:
        # In case no solution is found (should not happen given the puzzle constraints).
        print(json.dumps({"solution": "No solution found"}))
        
if __name__ == '__main__':
    main()