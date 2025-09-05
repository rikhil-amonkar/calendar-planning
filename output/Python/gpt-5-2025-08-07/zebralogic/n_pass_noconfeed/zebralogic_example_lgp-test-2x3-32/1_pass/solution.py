import json
from itertools import permutations

def solve_puzzle():
    # Input variables
    houses = [1, 2]  # House numbers from left (1) to right (2)
    names = ["Eric", "Arnold"]
    birthdays = ["sept", "april"]
    colors = ["yellow", "red"]

    solutions = []

    # Iterate over all permutations ensuring unique assignment per category
    for name_perm in permutations(names):
        for birthday_perm in permutations(birthdays):
            # Clue 2: The person whose birthday is in April is in the first house.
            if birthday_perm[0] != "april":
                continue

            for color_perm in permutations(colors):
                # Clue 3: The person who loves yellow is not in the first house.
                if color_perm[0] == "yellow":
                    continue

                # Clue 1: Eric is the person who loves yellow.
                eric_index = name_perm.index("Eric")
                if color_perm[eric_index] != "yellow":
                    continue

                # If all constraints satisfied, record solution
                assignment = []
                for i, house in enumerate(houses):
                    assignment.append({
                        "House": str(house),
                        "Name": name_perm[i],
                        "Birthday": birthday_perm[i],
                        "Color": color_perm[i],
                    })
                solutions.append(assignment)

    # Assuming unique solution
    if not solutions:
        raise ValueError("No solution found")
    solution = solutions[0]

    output = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Color"],
            "rows": [[row["House"], row["Name"], row["Birthday"], row["Color"]] for row in solution]
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False, indent=2))