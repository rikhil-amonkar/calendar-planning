import json
from itertools import permutations

def solve_puzzle():
    # Input variables
    houses = [1, 2]
    names = ["Eric", "Arnold"]
    birthdays = ["sept", "april"]
    colors = ["yellow", "red"]

    solutions = []

    # Iterate over all possible assignments using permutations (enforces uniqueness)
    for name_perm in permutations(names):
        name_by_house = {house: name_perm[i] for i, house in enumerate(houses)}

        for birthday_perm in permutations(birthdays):
            birthday_by_house = {house: birthday_perm[i] for i, house in enumerate(houses)}

            # Clue 2: The person whose birthday is in April is in the first house.
            if birthday_by_house[1] != "april":
                continue

            for color_perm in permutations(colors):
                color_by_house = {house: color_perm[i] for i, house in enumerate(houses)}

                # Clue 3: The person who loves yellow is not in the first house.
                if color_by_house[1] == "yellow":
                    continue

                # Clue 1: Eric is the person who loves yellow.
                # Find the house of Eric and check its color is yellow
                eric_house = next(h for h in houses if name_by_house[h] == "Eric")
                if color_by_house[eric_house] != "yellow":
                    continue

                # All constraints satisfied, build solution
                solution_rows = []
                for h in houses:
                    solution_rows.append([
                        str(h),
                        name_by_house[h],
                        birthday_by_house[h],
                        color_by_house[h],
                    ])
                solutions.append(solution_rows)

    # Assuming a unique solution for well-formed Zebra puzzles
    if not solutions:
        raise ValueError("No solution found.")
    if len(solutions) > 1:
        # In case multiple solutions exist, pick the first but this shouldn't happen for standard puzzles
        pass

    result = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Color"],
            "rows": solutions[0]
        }
    }
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))