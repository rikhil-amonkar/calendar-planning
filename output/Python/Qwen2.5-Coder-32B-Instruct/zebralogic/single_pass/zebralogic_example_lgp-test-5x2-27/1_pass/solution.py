import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]
    names = ["Peter", "Alice", "Bob", "Eric", "Arnold"]
    heights = ["very tall", "average", "tall", "very short", "short"]

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for height_perm in itertools.permutations(heights):
            # Create a list of dictionaries for each house
            solution = [{"House": h, "Name": n, "Height": ht} for h, n, ht in zip(houses, name_perm, height_perm)]

            # Check all constraints
            if (solution[1]["Height"] == "short" and
                solution[name_perm.index("Peter")] == {"House": solution[name_perm.index("Bob")]["House"] - 1, "Name": "Peter", "Height": solution[name_perm.index("Peter")]["Height"]} and
                solution[name_perm.index("Eric")]["House"] < solution[name_perm.index("Peter")]["House"] and
                solution[name_perm.index("Peter")]["House"] == solution[height_perm.index("very tall")]["House"] + 1 and
                solution[name_perm.index("Alice")]["House"] == solution[height_perm.index("average")]["House"] - 1 and
                abs(solution[height_perm.index("short")]["House"] - solution[height_perm.index("very short")]["House"]) == 1 and
                solution[height_perm.index("average")]["House"] == 5):
                
                # Format the solution as required
                result = {
                    "solution": {
                        "header": ["House", "Name", "Height"],
                        "rows": [[str(s["House"]), s["Name"], s["Height"]] for s in solution]
                    }
                }
                print(json.dumps(result))
                return

solve_puzzle()