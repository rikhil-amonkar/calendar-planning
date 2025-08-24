import json
import itertools

def solve_puzzle():
    # Houses are 1..4 from left (1) to right (4)
    houses = [1, 2, 3, 4]

    # Attributes
    names = ["Peter", "Arnold", "Alice", "Eric"]
    colors = ["yellow", "green", "red", "white"]

    # Helper to get index (house index 0..3) of a value in an assignment list
    def pos_of(assignment, value):
        return assignment.index(value)

    solutions = []

    # Iterate over all possible name assignments to houses
    # house_names[i] is the name in house (i+1)
    for house_names in itertools.permutations(names):
        # Constraint 2: Peter is in the first house.
        if house_names[0] != "Peter":
            continue

        # Constraint 4: Arnold is directly left of Eric.
        arnold_pos = pos_of(house_names, "Arnold")
        eric_pos = pos_of(house_names, "Eric")
        if arnold_pos + 1 != eric_pos:
            continue

        # Iterate over all possible color assignments to houses
        # house_colors[i] is the color of house (i+1)
        for house_colors in itertools.permutations(colors):
            # Constraint 1: The person whose favorite color is green is in the third house.
            if house_colors[2] != "green":
                continue

            # Constraint 5: Eric is the person who loves yellow.
            if house_colors[eric_pos] != "yellow":
                continue

            # Constraint 3: There is one house between the person who loves red and the person who loves yellow.
            red_pos = house_colors.index("red")
            yellow_pos = house_colors.index("yellow")
            if abs(red_pos - yellow_pos) != 2:
                continue

            # All constraints satisfied; record solution
            solutions.append((house_names, house_colors))

    if not solutions:
        raise ValueError("No solution found for the given puzzle constraints.")
    if len(solutions) > 1:
        # Still output the first, but it's informative to know multiple exist (not printed as per requirements).
        pass

    house_names, house_colors = solutions[0]

    result = {
        "solution": {
            "header": ["House", "Name", "Color"],
            "rows": [
                [str(h), house_names[h-1], house_colors[h-1]] for h in houses
            ]
        }
    }

    print(json.dumps(result, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve_puzzle()