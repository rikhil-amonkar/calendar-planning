import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]
    names = ["Peter", "Alice", "Bob", "Eric", "Arnold"]
    heights = ["very tall", "average", "tall", "very short", "short"]

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for height_perm in itertools.permutations(heights):
            # Create a list of dictionaries representing each house
            assignment = [{"house": h, "name": n, "height": ht} for h, n, ht in zip(houses, name_perm, height_perm)]

            # Check all constraints
            if (assignment[1]["height"] == "short" and
                assignment[name_perm.index("Peter")] == assignment[name_perm.index("Bob") - 1] and
                assignment[name_perm.index("Eric")]["house"] < assignment[name_perm.index("Peter")]["house"] and
                assignment[name_perm.index("Peter") - 1]["height"] == "very tall" and
                assignment[name_perm.index("Alice")] == assignment[height_perm.index("average") - 1] and
                abs(assignment[height_perm.index("short")]["house"] - assignment[height_perm.index("very short")]["house"]) == 1 and
                assignment[height_perm.index("average")]["house"] == 5):
                
                # Format the solution as required
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Height"],
                        "rows": [[str(a["house"]), a["name"], a["height"]] for a in assignment]
                    }
                }
                return json.dumps(solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())