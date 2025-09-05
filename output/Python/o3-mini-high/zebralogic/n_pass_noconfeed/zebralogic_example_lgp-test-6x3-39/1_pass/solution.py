import json

def valid(assignment):
    n = len(assignment)
    # Constraint 13 & 14: House 6 (index 5) must have child "Meredith" and smoothie "dragonfruit"
    if n >= 6:
        if assignment[5]["child"] != "Meredith" or assignment[5]["smoothie"] != "dragonfruit":
            return False

    # For each assigned house, check individual attribute constraints.
    for i, house in enumerate(assignment):
        # Constraint 6 & 7: If the mother's name is "Alice", then her child must be "Alice" and her smoothie must be "watermelon".
        if house["name"] == "Alice":
            if house["child"] != "Alice" or house["smoothie"] != "watermelon":
                return False
        # And if the child is "Alice", the mother's name must be "Alice".
        if house["child"] == "Alice" and house["name"] != "Alice":
            return False

        # Constraint 10: If the mother's name is "Bob", then her child must be "Timothy".
        if house["name"] == "Bob":
            if house["child"] != "Timothy":
                return False
        if house["child"] == "Timothy" and house["name"] != "Bob":
            return False

    # Constraint 11: "Arnold is directly left of Carol."
    for i in range(n - 1):
        if assignment[i]["name"] == "Arnold":
            if assignment[i+1]["name"] != "Carol":
                return False
        if assignment[i+1]["name"] == "Carol":
            if assignment[i]["name"] != "Arnold":
                return False

    # Constraint 12: "The person who likes Cherry smoothies is directly left of the person's child is named Samantha."
    for i in range(n - 1):
        if assignment[i]["smoothie"] == "cherry":
            if assignment[i+1]["child"] != "Samantha":
                return False
        if assignment[i+1]["child"] == "Samantha":
            if assignment[i]["smoothie"] != "cherry":
                return False

    # Constraint 1: The house with child "Fred" must be next to a house whose smoothie is "desert".
    for i, house in enumerate(assignment):
        if house["child"] == "Fred":
            neighbors = []
            if i - 1 >= 0:
                neighbors.append(assignment[i-1])
            if i + 1 < n:
                neighbors.append(assignment[i+1])
            # Only check if at least one neighbor is assigned.
            if neighbors:
                if all(neighbor["smoothie"] != "desert" for neighbor in neighbors):
                    return False

    # Constraint 2: "The person who drinks Blueberry smoothies is somewhere to the left of the person whose child is named Fred."
    index_blueberry = None
    index_fred = None
    for i, house in enumerate(assignment):
        if house["smoothie"] == "blueberry":
            index_blueberry = i
        if house["child"] == "Fred":
            index_fred = i
    if index_blueberry is not None and index_fred is not None:
        if index_blueberry >= index_fred:
            return False

    # Constraint 5: "The Watermelon smoothie lover is somewhere to the right of the person who likes Cherry smoothies."
    index_watermelon = None
    index_cherry = None
    for i, house in enumerate(assignment):
        if house["smoothie"] == "watermelon":
            index_watermelon = i
        if house["smoothie"] == "cherry":
            index_cherry = i
    if index_watermelon is not None and index_cherry is not None:
        if index_cherry >= index_watermelon:
            return False

    # Constraint 8: "Peter is somewhere to the right of the person whose child is named Samantha."
    index_peter = None
    index_samantha = None
    for i, house in enumerate(assignment):
        if house["name"] == "Peter":
            index_peter = i
        if house["child"] == "Samantha":
            index_samantha = i
    if index_peter is not None and index_samantha is not None:
        if index_peter <= index_samantha:
            return False

    return True

def backtrack(i, assignment, available_names, available_children, available_smoothies):
    if i == 6:
        if valid(assignment):
            return assignment
        else:
            return None

    for n in available_names:
        # Constraint 9: "Arnold is not in the second house." (house index 1)
        if i == 1 and n == "Arnold":
            continue
        # Constraint 3: "Alice is not in the fifth house." (house index 4)
        if i == 4 and n == "Alice":
            continue

        for c in available_children:
            # Constraint 4: "The person whose child is named Samantha is not in the second house." (house index 1)
            if i == 1 and c == "Samantha":
                continue
            # Constraint 13: "The person whose child is named Meredith is in the sixth house." (house index 5)
            if i == 5 and c != "Meredith":
                continue
            # Enforce the bi-directional rule for "Alice".
            if n == "Alice" and c != "Alice":
                continue
            if c == "Alice" and n != "Alice":
                continue
            # Enforce the rule for "Bob".
            if n == "Bob" and c != "Timothy":
                continue
            if c == "Timothy" and n != "Bob":
                continue

            for s in available_smoothies:
                # Constraint 14: In the sixth house (index 5), the smoothie must be "dragonfruit".
                if i == 5 and s != "dragonfruit":
                    continue
                # For "Alice", the smoothie must be "watermelon".
                if n == "Alice" and s != "watermelon":
                    continue
                if s == "watermelon" and n != "Alice":
                    continue

                # Construct the candidate house.
                house = {"name": n, "child": c, "smoothie": s}
                assignment.append(house)
                new_names = available_names.copy()
                new_names.remove(n)
                new_children = available_children.copy()
                new_children.remove(c)
                new_smoothies = available_smoothies.copy()
                new_smoothies.remove(s)
                if valid(assignment):
                    result = backtrack(i + 1, assignment, new_names, new_children, new_smoothies)
                    if result is not None:
                        return result
                assignment.pop()
    return None

def solve():
    names = ["Arnold", "Peter", "Carol", "Alice", "Bob", "Eric"]
    children = ["Alice", "Timothy", "Bella", "Meredith", "Fred", "Samantha"]
    smoothies = ["desert", "cherry", "watermelon", "blueberry", "lime", "dragonfruit"]
    assignment = []
    solution = backtrack(0, assignment, names, children, smoothies)
    return solution

if __name__ == "__main__":
    sol = solve()
    if sol is None:
        output = {"solution": {"header": ["House", "Name", "Children", "Smoothie"], "rows": []}}
    else:
        rows = []
        for i, house in enumerate(sol):
            # House numbering is from 1 to 6.
            rows.append([str(i + 1), house["name"], house["child"], house["smoothie"]])
        output = {
            "solution": {
                "header": ["House", "Name", "Children", "Smoothie"],
                "rows": rows
            }
        }
    print(json.dumps(output, indent=2))