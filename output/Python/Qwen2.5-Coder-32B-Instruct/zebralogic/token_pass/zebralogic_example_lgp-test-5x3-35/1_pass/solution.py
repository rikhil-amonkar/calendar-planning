import json

def solve_puzzle():
    # Initialize the houses with all possible values
    houses = [
        {"house": 1, "name": {"Eric", "Peter", "Arnold", "Alice", "Bob"},
         "mother": {"Kailyn", "Janelle", "Aniya", "Penny", "Holly"},
         "height": {"average", "very short", "short", "very tall", "tall"}},
        {"house": 2, "name": {"Eric", "Peter", "Arnold", "Alice", "Bob"},
         "mother": {"Kailyn", "Janelle", "Aniya", "Penny", "Holly"},
         "height": {"average", "very short", "short", "very tall", "tall"}},
        {"house": 3, "name": {"Eric", "Peter", "Arnold", "Alice", "Bob"},
         "mother": {"Kailyn", "Janelle", "Aniya", "Penny", "Holly"},
         "height": {"average", "very short", "short", "very tall", "tall"}},
        {"house": 4, "name": {"Eric", "Peter", "Arnold", "Alice", "Bob"},
         "mother": {"Kailyn", "Janelle", "Aniya", "Penny", "Holly"},
         "height": {"average", "very short", "short", "very tall", "tall"}},
        {"house": 5, "name": {"Eric", "Peter", "Arnold", "Alice", "Bob"},
         "mother": {"Kailyn", "Janelle", "Aniya", "Penny", "Holly"},
         "height": {"average", "very short", "short", "very tall", "tall"}}
    ]

    # Apply constraints
    # Constraint 1: Alice is The person whose mother's name is Aniya.
    for house in houses:
        if "Alice" in house["name"] and "Aniya" in house["mother"]:
            house["name"] = {"Alice"}
            house["mother"] = {"Aniya"}
            break

    # Constraint 3: The person whose mother's name is Janelle is Bob.
    for house in houses:
        if "Bob" in house["name"] and "Janelle" in house["mother"]:
            house["name"] = {"Bob"}
            house["mother"] = {"Janelle"}
            break

    # Constraint 6: The person who is very tall is Arnold.
    for house in houses:
        if "Arnold" in house["name"] and "very tall" in house["height"]:
            house["name"] = {"Arnold"}
            house["height"] = {"very tall"}
            break

    # Constraint 10: Eric is The person whose mother's name is Kailyn.
    for house in houses:
        if "Eric" in house["name"] and "Kailyn" in house["mother"]:
            house["name"] = {"Eric"}
            house["mother"] = {"Kailyn"}
            break

    # Constraint 11: The person who is very short is in the fifth house.
    houses[4]["height"] = {"very short"}

    # Constraint 4: Peter is not in the second house.
    houses[1]["name"].discard("Peter")

    # Constraint 8: Eric is not in the fifth house.
    houses[4]["name"].discard("Eric")

    # Constraint 7: Bob is directly left of the person who has an average height.
    for i in range(len(houses) - 1):
        if "Bob" in houses[i]["name"] and "average" in houses[i + 1]["height"]:
            houses[i]["name"] = {"Bob"}
            houses[i + 1]["height"] = {"average"}
            break

    # Constraint 5: The person who is short is directly left of Arnold.
    for i in range(len(houses) - 1):
        if "short" in houses[i]["height"] and "Arnold" in houses[i + 1]["name"]:
            houses[i]["height"] = {"short"}
            houses[i + 1]["name"] = {"Arnold"}
            break

    # Constraint 2: The person who has an average height is somewhere to the left of The person whose mother's name is Penny.
    for i in range(len(houses)):
        if "average" in houses[i]["height"]:
            for j in range(i + 1, len(houses)):
                if "Penny" in houses[j]["mother"]:
                    houses[i]["height"] = {"average"}
                    houses[j]["mother"] = {"Penny"}
                    break

    # Constraint 9: The person who is very tall is somewhere to the right of The person whose mother's name is Holly.
    for i in range(len(houses)):
        if "Holly" in houses[i]["mother"]:
            for j in range(i + 1, len(houses)):
                if "very tall" in houses[j]["height"]:
                    houses[i]["mother"] = {"Holly"}
                    houses[j]["height"] = {"very tall"}
                    break

    # Final validation and deduction
    for house in houses:
        for key in house:
            if isinstance(house[key], set) and len(house[key]) == 1:
                house[key] = list(house[key])[0]

    # Construct the solution in the required format
    solution = {
        "solution": {
            "header": ["House", "Name", "Mother", "Height"],
            "rows": [[str(house["house"]), house["name"], house["mother"], house["height"]] for house in houses]
        }
    }

    return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())