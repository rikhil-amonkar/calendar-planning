import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Bob", "Peter", "Eric", "Alice", "Arnold", "Carol"]
    hair_colors = ["auburn", "blonde", "brown", "black", "red", "gray"]
    heights = ["very tall", "average", "very short", "tall", "super tall", "short"]

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for hair_color_perm in itertools.permutations(hair_colors):
            for height_perm in itertools.permutations(heights):
                # Create a list of dictionaries for each house
                assignment = [
                    {"house": h, "name": n, "hair_color": c, "height": ht}
                    for h, n, c, ht in zip(houses, name_perm, hair_color_perm, height_perm)
                ]

                # Check each clue
                if (assignment[assignment.index(next(x for x in assignment if x["name"] == "Carol"))]["hair_color"] == "blonde" and
                    assignment[assignment.index(next(x for x in assignment if x["name"] == "Carol")) + 1]["name"] == "Bob" and
                    assignment[3]["name"] == "Alice" and
                    assignment[assignment.index(next(x for x in assignment if x["name"] == "Arnold"))]["height"] == "short" and
                    assignment[5]["height"] == "tall" and
                    assignment[3]["hair_color"] != "black" and
                    assignment[assignment.index(next(x for x in assignment if x["name"] == "Eric"))]["hair_color"] == "red" and
                    assignment[assignment.index(next(x for x in assignment if x["height"] == "average")) + 1:].count(next(x for x in assignment if x["height"] == "super tall")) > 0 and
                    assignment[assignment.index(next(x for x in assignment if x["name"] == "Carol"))]["hair_color"] == "blonde" and
                    assignment[assignment.index(next(x for x in assignment if x["name"] == "Carol"))]["height"] == "very tall" and
                    abs(assignment.index(next(x for x in assignment if x["hair_color"] == "gray")) - assignment.index(next(x for x in assignment if x["hair_color"] == "red"))) == 2 and
                    assignment[4]["height"] == "very short" and
                    assignment[assignment.index(next(x for x in assignment if x["name"] == "Bob"))]["hair_color"] == "brown" and
                    assignment[2]["hair_color"] == "gray"):
                    
                    # If all clues are satisfied, format the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "HairColor", "Height"],
                            "rows": [[str(a["house"]), a["name"], a["hair_color"], a["height"]] for a in assignment]
                        }
                    }
                    return json.dumps(solution)

# Run the solver and print the result
print(solve_puzzle())