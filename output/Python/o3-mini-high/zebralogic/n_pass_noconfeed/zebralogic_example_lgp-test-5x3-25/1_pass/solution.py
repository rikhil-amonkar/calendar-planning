import itertools
import json

def main():
    names = ["Arnold", "Bob", "Alice", "Eric", "Peter"]
    heights = ["very tall", "average", "tall", "very short", "short"]
    foods = ["stew", "grilled cheese", "spaghetti", "pizza", "stir fry"]

    solution = None

    for perm_names in itertools.permutations(names):
        # Constraint: House 3 (index 2) must be Eric.
        if perm_names[2] != "Eric":
            continue
        # Constraint: Bob is somewhere to the right of Arnold.
        if perm_names.index("Bob") <= perm_names.index("Arnold"):
            continue

        for perm_heights in itertools.permutations(heights):
            # Constraint: House 3 (index 2) must be "tall".
            if perm_heights[2] != "tall":
                continue

            valid = True
            # Constraint: Alice is the person who is short.
            for i in range(5):
                if perm_names[i] == "Alice" and perm_heights[i] != "short":
                    valid = False
                    break
                if perm_heights[i] == "short" and perm_names[i] != "Alice":
                    valid = False
                    break
            if not valid:
                continue

            # Constraint: The person who has an average height is not in the second house.
            if perm_heights[1] == "average":
                continue

            # Constraint: The person who is very short is somewhere to the left of Arnold.
            index_vshort = perm_heights.index("very short")
            if index_vshort >= perm_names.index("Arnold"):
                continue

            # Constraint: Eric is the person who is tall.
            if perm_heights[perm_names.index("Eric")] != "tall":
                continue

            for perm_foods in itertools.permutations(foods):
                # Constraint: House 3 (index 2) must have pizza since the tall person loves pizza.
                if perm_foods[2] != "pizza":
                    continue

                food_valid = True
                # Constraint: The person who loves stir fry is Arnold.
                for i in range(5):
                    if perm_names[i] == "Arnold" and perm_foods[i] != "stir fry":
                        food_valid = False
                        break
                    if perm_foods[i] == "stir fry" and perm_names[i] != "Arnold":
                        food_valid = False
                        break
                if not food_valid:
                    continue

                # Constraint: The person who is a pizza lover is the person who is tall.
                for i in range(5):
                    if perm_foods[i] == "pizza" and perm_heights[i] != "tall":
                        food_valid = False
                        break
                    if perm_heights[i] == "tall" and perm_foods[i] != "pizza":
                        food_valid = False
                        break
                if not food_valid:
                    continue

                # Constraint: The person who has an average height is somewhere to the left of the person who loves stew.
                index_average = perm_heights.index("average")
                index_stew = perm_foods.index("stew")
                if index_average >= index_stew:
                    continue

                # Constraint: The person who loves eating grilled cheese is somewhere to the right of Eric.
                index_gc = perm_foods.index("grilled cheese")
                if index_gc <= perm_names.index("Eric"):
                    continue

                # All constraints satisfied. Build the solution.
                solution = []
                for i in range(5):
                    solution.append([str(i+1), perm_names[i], perm_heights[i], perm_foods[i]])
                break
            if solution is not None:
                break
        if solution is not None:
            break

    output = {
        "solution": {
            "header": ["House", "Name", "Height", "Food"],
            "rows": solution
        }
    }
    print(json.dumps(output))

if __name__ == '__main__':
    main()