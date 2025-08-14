#!/usr/bin/env python3
import json
import itertools

def main():
    # Define the houses and possible attributes as given in the puzzle
    houses = [1, 2]
    names = ["Arnold", "Eric"]
    vacations = ["beach", "mountain"]

    # This list will hold all assignments that satisfy the constraints.
    valid_assignments = []

    # Iterate over all permutations for names and vacations.
    for name_perm in itertools.permutations(names):
        for vac_perm in itertools.permutations(vacations):
            # Build an assignment dictionary for each house
            assignment = {}
            for i, house in enumerate(houses):
                assignment[house] = {
                    "Name": name_perm[i],
                    "vacation": vac_perm[i]
                }

            # Constraint: "Arnold is somewhere to the right of the person who loves beach vacations."
            arnold_house = None
            beach_house = None
            for house in houses:
                if assignment[house]["Name"] == "Arnold":
                    arnold_house = house
                if assignment[house]["vacation"] == "beach":
                    beach_house = house

            # Check if both were assigned and Arnold is to the right of the beach lover.
            if arnold_house is not None and beach_house is not None:
                if arnold_house > beach_house:
                    valid_assignments.append(assignment)

    # Assume there is one unique solution; we take the first valid assignment.
    if valid_assignments:
        solution = valid_assignments[0]
        sorted_houses = sorted(solution.keys())
        header = ["House", "Name", "vacation"]
        rows = []
        for house in sorted_houses:
            row = [str(house), solution[house]["Name"], solution[house]["vacation"]]
            rows.append(row)
        output = {"solution": {"header": header, "rows": rows}}
    else:
        output = {"solution": {"header": [], "rows": []}}

    print(json.dumps(output))

if __name__ == "__main__":
    main()