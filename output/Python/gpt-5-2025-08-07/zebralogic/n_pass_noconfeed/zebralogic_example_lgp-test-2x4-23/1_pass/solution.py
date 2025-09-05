import json
from itertools import permutations

def solve_puzzle():
    # Input variables (as per puzzle)
    houses = [1, 2]  # Left (1) to Right (2)
    names = ["Eric", "Arnold"]
    mothers = ["Aniya", "Holly"]
    car_models = ["ford f150", "tesla model 3"]
    heights = ["short", "very short"]

    solutions = []

    # Enumerate all possible assignments using permutations
    for names_perm in permutations(names):
        for mothers_perm in permutations(mothers):
            # Clue 3 optimization: Holly is in the second house
            if mothers_perm[houses.index(2)] != "Holly":
                continue

            for cars_perm in permutations(car_models):
                for heights_perm in permutations(heights):
                    # Build mapping from house -> attributes
                    assignments = {
                        house: {
                            "Name": names_perm[i],
                            "Mother": mothers_perm[i],
                            "CarModel": cars_perm[i],
                            "Height": heights_perm[i],
                        }
                        for i, house in enumerate(houses)
                    }

                    # Helper to find house index by attribute
                    def house_of(attribute, value):
                        for h in houses:
                            if assignments[h][attribute] == value:
                                return h
                        return None

                    # Apply Clues
                    # 1. Tesla owner is somewhere to the right of Arnold
                    arnold_house = house_of("Name", "Arnold")
                    tesla_house = house_of("CarModel", "tesla model 3")
                    if not (tesla_house is not None and arnold_house is not None and tesla_house > arnold_house):
                        continue

                    # 2. Arnold is the person who is short
                    if assignments[arnold_house]["Height"] != "short":
                        continue

                    # 3. Already enforced above: "Holly" is in the second house

                    solutions.append(assignments)

    if not solutions:
        raise RuntimeError("No solution found for the given puzzle.")
    if len(solutions) > 1:
        # If multiple solutions exist, we can still output the first,
        # but ideally puzzles should be uniquely solvable.
        pass

    # Use the first (or only) solution
    sol = solutions[0]

    # Prepare output
    header = ["House", "Name", "Mother", "CarModel", "Height"]
    rows = []
    for h in sorted(houses):
        row = [
            str(h),
            sol[h]["Name"],
            sol[h]["Mother"],
            sol[h]["CarModel"],
            sol[h]["Height"],
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))