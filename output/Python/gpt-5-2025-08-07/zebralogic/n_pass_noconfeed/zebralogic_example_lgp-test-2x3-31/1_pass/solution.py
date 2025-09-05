import itertools
import json

def solve_puzzle():
    # Define houses and attributes
    houses = [1, 2]  # Left to right
    names = ["Eric", "Arnold"]
    sports = ["basketball", "soccer"]
    hobbies = ["photography", "gardening"]

    solutions = []

    # Iterate over all permutations ensuring uniqueness per attribute across houses
    for name_perm in itertools.permutations(names):
        name_by_house = {house: name_perm[i] for i, house in enumerate(houses)}

        for sport_perm in itertools.permutations(sports):
            sport_by_house = {house: sport_perm[i] for i, house in enumerate(houses)}

            for hobby_perm in itertools.permutations(hobbies):
                hobby_by_house = {house: hobby_perm[i] for i, house in enumerate(houses)}

                # Apply constraints:

                # 1. The person who enjoys gardening is Arnold.
                valid = True
                for h in houses:
                    if hobby_by_house[h] == "gardening" and name_by_house[h] != "Arnold":
                        valid = False
                        break
                    if name_by_house[h] == "Arnold" and hobby_by_house[h] != "gardening":
                        valid = False
                        break
                if not valid:
                    continue

                # 2. The photography enthusiast is not in the first house.
                if hobby_by_house[1] == "photography":
                    continue

                # 3. The person who loves soccer is not in the first house.
                if sport_by_house[1] == "soccer":
                    continue

                # If all constraints are satisfied, record solution
                solutions.append({
                    h: {
                        "Name": name_by_house[h],
                        "FavoriteSport": sport_by_house[h],
                        "Hobby": hobby_by_house[h],
                    }
                    for h in houses
                })

    # Expect exactly one solution
    if not solutions:
        raise ValueError("No solution found.")
    if len(solutions) > 1:
        # In case multiple solutions, we still output the first one deterministically
        solution = solutions[0]
    else:
        solution = solutions[0]

    # Prepare JSON output
    output = {
        "solution": {
            "header": ["House", "Name", "FavoriteSport", "Hobby"],
            "rows": [
                [str(h), solution[h]["Name"], solution[h]["FavoriteSport"], solution[h]["Hobby"]]
                for h in sorted(houses)
            ],
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))