import itertools
import json

def solve_puzzle():
    # Input variables
    houses = [1, 2]  # House numbers from left (1) to right (2)
    names = ["Eric", "Arnold"]
    sports = ["basketball", "soccer"]
    hobbies = ["photography", "gardening"]

    solutions = []

    # Try all permutations for each attribute category
    for name_perm in itertools.permutations(names):
        for sport_perm in itertools.permutations(sports):
            for hobby_perm in itertools.permutations(hobbies):
                # Build house assignments
                house_data = []
                for i, h in enumerate(houses):
                    house_data.append({
                        "House": str(h),
                        "Name": name_perm[i],
                        "FavoriteSport": sport_perm[i],
                        "Hobby": hobby_perm[i],
                    })

                # Apply constraints:

                # 1. The person who enjoys gardening is Arnold.
                gardening_house = next(i for i, hd in enumerate(house_data) if hd["Hobby"] == "gardening")
                if house_data[gardening_house]["Name"] != "Arnold":
                    continue

                # 2. The photography enthusiast is not in the first house.
                if house_data[0]["Hobby"] == "photography":
                    continue

                # 3. The person who loves soccer is not in the first house.
                if house_data[0]["FavoriteSport"] == "soccer":
                    continue

                solutions.append(house_data)

    if not solutions:
        raise ValueError("No solution found.")
    if len(solutions) > 1:
        # If multiple solutions exist, we still output the first, but it's unexpected for a well-posed puzzle.
        pass

    solution = solutions[0]
    header = ["House", "Name", "FavoriteSport", "Hobby"]
    rows = [[row[h] for h in header] for row in solution]

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