import itertools
import json

def solve_puzzle():
    # Define the attributes
    houses = [1, 2]
    names = ["Arnold", "Eric"]
    vacations = ["beach", "mountain"]

    # Generate all possible permutations of names and vacations
    for name_perm in itertools.permutations(names):
        for vac_perm in itertools.permutations(vacations):
            # Assign attributes to houses
            solution = []
            for i in range(2):
                house = {
                    "House": str(i + 1),
                    "Name": name_perm[i],
                    "Vacation": vac_perm[i]
                }
                solution.append(house)

            # Check the clues
            # Clue 1: Arnold is somewhere to the right of the person who loves beach vacations
            beach_house = None
            arnold_house = None
            for house in solution:
                if house["Vacation"] == "beach":
                    beach_house = house["House"]
                if house["Name"] == "Arnold":
                    arnold_house = house["House"]
            if beach_house is not None and arnold_house is not None:
                if int(arnold_house) > int(beach_house):
                    # Prepare the output
                    output = {
                        "solution": {
                            "header": ["House", "Name", "Vacation"],
                            "rows": [
                                [str(1), name_perm[0], vac_perm[0]],
                                [str(2), name_perm[1], vac_perm[1]]
                            ]
                        }
                    }
                    return output

    return {"solution": {"header": [], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))