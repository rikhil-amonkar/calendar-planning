import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]
    names = ["Bob", "Eric", "Arnold", "Alice", "Peter"]
    colors = ["blue", "green", "white", "yellow", "red"]
    phones = ["huawei p50", "samsung galaxy s21", "oneplus 9", "iphone 13", "google pixel 6"]
    occupations = ["artist", "teacher", "doctor", "engineer", "lawyer"]

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for color_perm in itertools.permutations(colors):
            for phone_perm in itertools.permutations(phones):
                for occupation_perm in itertools.permutations(occupations):
                    # Create a list of dictionaries for each house
                    solution = [
                        {"House": houses[i], "Name": name_perm[i], "Color": color_perm[i], 
                         "Phone": phone_perm[i], "Occupation": occupation_perm[i]}
                        for i in range(5)
                    ]

                    # Check all constraints
                    if (solution.index(next(x for x in solution if x["Occupation"] == "engineer")) >
                        solution.index(next(x for x in solution if x["Occupation"] == "lawyer")) and
                        solution[1]["Name"] == "Bob" and
                        next(x for x in solution if x["Occupation"] == "doctor")["Phone"] == "samsung galaxy s21" and
                        next(x for x in solution if x["Occupation"] == "doctor")["Color"] == "blue" and
                        solution[4]["Color"] != "green" and
                        next(x for x in solution if x["Occupation"] == "lawyer")["Phone"] == "oneplus 9" and
                        solution.index(next(x for x in solution if x["Color"] == "blue")) + 1 ==
                        solution.index(next(x for x in solution if x["Color"] == "red")) and
                        solution.index(next(x for x in solution if x["Occupation"] == "lawyer")) >
                        solution.index(next(x for x in solution if x["Phone"] == "samsung galaxy s21")) and
                        abs(solution.index(next(x for x in solution if x["Phone"] == "google pixel 6")) -
                            solution.index(next(x for x in solution if x["Phone"] == "huawei p50"))) == 2 and
                        next(x for x in solution if x["Occupation"] == "engineer")["Name"] == "Arnold" and
                        next(x for x in solution if x["Color"] == "yellow")["Name"] == "Alice" and
                        next(x for x in solution if x["Phone"] == "google pixel 6")["Name"] == "Eric" and
                        next(x for x in solution if x["Phone"] == "google pixel 6")["Occupation"] == "teacher" and
                        solution.index(next(x for x in solution if x["Color"] == "red")) >
                        solution.index(next(x for x in solution if x["Occupation"] == "teacher"))):
                        
                        # Format the solution as required
                        formatted_solution = {
                            "solution": {
                                "header": ["House", "Name", "Color", "Phone", "Occupation"],
                                "rows": [
                                    [str(house), name, color, phone, occupation]
                                    for house, name, color, phone, occupation in zip(
                                        houses, name_perm, color_perm, phone_perm, occupation_perm
                                    )
                                ]
                            }
                        }
                        return json.dumps(formatted_solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())