import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]
    names = ["Eric", "Peter", "Arnold", "Alice", "Bob"]
    mothers = ["Kailyn", "Janelle", "Aniya", "Penny", "Holly"]
    heights = ["average", "very short", "short", "very tall", "tall"]

    # Generate all possible permutations for each category
    for name_perm in itertools.permutations(names):
        for mother_perm in itertools.permutations(mothers):
            for height_perm in itertools.permutations(heights):
                # Create a list of dictionaries for each house
                assignments = [
                    {"house": h, "name": n, "mother": m, "height": ht}
                    for h, n, m, ht in zip(houses, name_perm, mother_perm, height_perm)
                ]

                # Check each clue
                if (
                    # Clue 1
                    any(a["name"] == "Alice" and a["mother"] == "Aniya" for a in assignments) and
                    # Clue 2
                    any(assignments[i]["mother"] == "Penny" and assignments[j]["height"] == "average" for i in range(1, 5) for j in range(i)) and
                    # Clue 3
                    any(a["name"] == "Bob" and a["mother"] == "Janelle" for a in assignments) and
                    # Clue 4
                    not any(a["name"] == "Peter" and a["house"] == 2 for a in assignments) and
                    # Clue 5
                    any(assignments[i]["name"] == "Arnold" and assignments[j]["height"] == "short" for i in range(1, 5) for j in range(i+1) if assignments[j]["house"] == assignments[i]["house"] + 1) and
                    # Clue 6
                    any(a["name"] == "Arnold" and a["height"] == "very tall" for a in assignments) and
                    # Clue 7
                    any(assignments[i]["name"] == "Bob" and assignments[j]["height"] == "average" for i in range(1, 5) for j in range(i+1) if assignments[j]["house"] == assignments[i]["house"] + 1) and
                    # Clue 8
                    not any(a["name"] == "Eric" and a["house"] == 5 for a in assignments) and
                    # Clue 9
                    any(assignments[i]["mother"] == "Holly" and assignments[j]["height"] == "very tall" for i in range(4) for j in range(i+1, 5)) and
                    # Clue 10
                    any(a["name"] == "Eric" and a["mother"] == "Kailyn" for a in assignments) and
                    # Clue 11
                    any(a["height"] == "very short" and a["house"] == 5 for a in assignments)
                ):
                    # If all clues are satisfied, format the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Mother", "Height"],
                            "rows": [[str(a["house"]), a["name"], a["mother"], a["height"]] for a in assignments]
                        }
                    }
                    return json.dumps(solution, indent=2)

# Print the solution
print(solve_puzzle())