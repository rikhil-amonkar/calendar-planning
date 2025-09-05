import json
import itertools

def main():
    houses = [1, 2]
    names = ["Arnold", "Eric"]
    vacations = ["beach", "mountain"]

    solutions = []

    # Generate all possible assignments of names and vacations to houses.
    for name_perm in itertools.permutations(names):
        for vac_perm in itertools.permutations(vacations):
            assignment = {}
            for i, house in enumerate(houses):
                assignment[house] = {"Name": name_perm[i], "Vacation": vac_perm[i]}
            
            # Constraint 1: "Arnold is somewhere to the right of the person who loves beach vacations."
            # That implies the house number of Arnold must be greater than the house number of the person with beach vacations.
            pos_arnold = None
            pos_beach = None
            for house in houses:
                if assignment[house]["Name"] == "Arnold":
                    pos_arnold = house
                if assignment[house]["Vacation"] == "beach":
                    pos_beach = house
            
            if pos_arnold is not None and pos_beach is not None and pos_arnold > pos_beach:
                solutions.append(assignment)

    # Assuming there is exactly one valid solution, we select the first one.
    if solutions:
        solution = solutions[0]
        result_rows = []
        # Ensure rows are ordered by the house number.
        for house in houses:
            row = [str(house), solution[house]["Name"], solution[house]["Vacation"]]
            result_rows.append(row)
        
        output = {
            "solution": {
                "header": ["House", "Name", "Vacation"],
                "rows": result_rows
            }
        }
        print(json.dumps(output))
    else:
        print(json.dumps({"solution": "No valid solution found."}))

if __name__ == "__main__":
    main()