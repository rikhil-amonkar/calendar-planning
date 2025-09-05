import json

names_all = ["Bob", "Peter", "Eric", "Alice", "Arnold", "Carol"]
hair_all = ["auburn", "blonde", "brown", "black", "red", "gray"]
heights_all = ["very tall", "average", "very short", "tall", "super tall", "short"]

def valid_partial(assignment):
    n = len(assignment)
    for j, house in enumerate(assignment):
        # Fixed-position constraints
        if j == 2 and house["hair"] != "gray":
            return False
        if j == 3:
            if house["name"] != "Alice":
                return False
            if house["hair"] == "black":
                return False
        if j == 4 and house["height"] != "very short":
            return False
        if j == 5 and house["height"] != "tall":
            return False

        # Neighbor constraint for blonde hair and Bob
        if j > 0:
            prev = assignment[j-1]
            if prev.get("hair") == "blonde":
                # if the left house has blonde hair, then current house must be Bob.
                if house.get("name") is not None and house["name"] != "Bob":
                    return False
            if house.get("name") == "Bob":
                if prev.get("hair") is not None and prev["hair"] != "blonde":
                    return False

        # Constraint: The person with blonde hair is Carol.
        if house.get("hair") == "blonde" and house.get("name") != "Carol":
            return False
        if house.get("name") == "Carol" and house.get("hair") != "blonde":
            return False

        # Constraint: The person with blonde hair is very tall.
        if house.get("hair") == "blonde" and house.get("height") != "very tall":
            return False
        if house.get("height") == "very tall" and house.get("hair") != "blonde":
            return False

        # Constraint: Bob has brown hair.
        if house.get("name") == "Bob" and house.get("hair") != "brown":
            return False
        if house.get("hair") == "brown" and house.get("name") != "Bob":
            return False

        # Constraint: The person with red hair is Eric.
        if house.get("hair") == "red" and house.get("name") != "Eric":
            return False
        if house.get("name") == "Eric" and house.get("hair") != "red":
            return False

        # Constraint: The person who is short is Arnold.
        if house.get("height") == "short" and house.get("name") != "Arnold":
            return False
        if house.get("name") == "Arnold" and house.get("height") != "short":
            return False

        # Constraint: There is one house between the person with gray hair and red hair.
        # Gray hair is fixed in house index 2. So if a house is red-haired, its index must differ by 2 from 2.
        if house.get("hair") == "red":
            if abs(j - 2) != 2:
                return False

    # Constraint: The person who is super tall is somewhere to the right of the person who is average.
    avg_index = None
    super_tall_index = None
    for idx, house in enumerate(assignment):
        if house.get("height") == "average":
            avg_index = idx
        if house.get("height") == "super tall":
            super_tall_index = idx
    if avg_index is not None and super_tall_index is not None:
        if super_tall_index <= avg_index:
            return False

    return True

def backtrack(i, assignment, names_left, hair_left, heights_left):
    if i == 6:
        # Complete assignment reached.
        if valid_partial(assignment):
            return assignment
        else:
            return None

    # Determine candidate sets for current house based on fixed positions
    if i == 3:
        # Fourth house must be Alice.
        if "Alice" in names_left:
            possible_names = ["Alice"]
        else:
            return None
    else:
        possible_names = names_left[:]

    if i == 2:
        # Third house must have gray hair.
        if "gray" in hair_left:
            possible_hairs = ["gray"]
        else:
            return None
    elif i == 3:
        # Fourth house: hair cannot be black.
        possible_hairs = [h for h in hair_left if h != "black"]
    else:
        possible_hairs = hair_left[:]

    if i == 4:
        # Fifth house must be very short.
        if "very short" in heights_left:
            possible_heights = ["very short"]
        else:
            return None
    elif i == 5:
        # Sixth house must be tall.
        if "tall" in heights_left:
            possible_heights = ["tall"]
        else:
            return None
    else:
        possible_heights = heights_left[:]

    # Try all combinations for current house.
    for n in possible_names:
        for hair in possible_hairs:
            for ht in possible_heights:
                house = {"name": n, "hair": hair, "height": ht}
                new_assignment = assignment + [house]
                # Update remaining sets
                new_names = names_left[:]
                new_names.remove(n)
                new_hair = hair_left[:]
                new_hair.remove(hair)
                new_heights = heights_left[:]
                new_heights.remove(ht)

                if valid_partial(new_assignment):
                    result = backtrack(i + 1, new_assignment, new_names, new_hair, new_heights)
                    if result is not None:
                        return result
    return None

def solve_puzzle():
    solution_assignment = backtrack(0, [], names_all, hair_all, heights_all)
    if solution_assignment is None:
        return {"solution": {"header": ["House", "Name", "HairColor", "Height"], "rows": []}}
    
    # Format the solution as required.
    rows = []
    # Houses are numbered 1 to 6 (assignment indices 0-5)
    for idx, house in enumerate(solution_assignment):
        row = [str(idx + 1), house["name"], house["hair"], house["height"]]
        rows.append(row)
    return {
        "solution": {
            "header": ["House", "Name", "HairColor", "Height"],
            "rows": rows
        }
    }

if __name__ == "__main__":
    sol = solve_puzzle()
    print(json.dumps(sol))