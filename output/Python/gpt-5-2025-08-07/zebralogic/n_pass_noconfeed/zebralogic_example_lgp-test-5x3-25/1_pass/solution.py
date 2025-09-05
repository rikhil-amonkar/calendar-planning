import json
import itertools

def solve_puzzle():
    houses = [0, 1, 2, 3, 4]  # indices for houses 1..5

    names_all = ["Arnold", "Bob", "Alice", "Eric", "Peter"]
    heights_all = ["very tall", "average", "tall", "very short", "short"]
    foods_all = ["stew", "grilled cheese", "spaghetti", "pizza", "stir fry"]

    solutions = []

    # Pre-assignments from clues:
    # - House 3 (index 2) has: tall, pizza, Eric
    fixed_house_index = 2
    fixed_height = "tall"
    fixed_food = "pizza"
    fixed_name = "Eric"

    # Names: fix Eric at house 3
    other_names = [n for n in names_all if n != fixed_name]
    for perm_names in itertools.permutations(other_names):
        names = [None] * 5
        # fill names except index 2
        fill_indices = [i for i in houses if i != fixed_house_index]
        for idx, name in zip(fill_indices, perm_names):
            names[idx] = name
        names[fixed_house_index] = fixed_name

        # Clue 8: Bob right of Arnold
        idx_arnold = names.index("Arnold")
        idx_bob = names.index("Bob")
        if not (idx_bob > idx_arnold):
            continue

        # Clue 5 implies Arnold cannot be at house 1 because of clue 10 (very short left of Arnold)
        # This will be enforced with heights, but we can keep going.

        # Heights: fix tall at house 3
        other_heights = [h for h in heights_all if h != fixed_height]
        for perm_heights in itertools.permutations(other_heights):
            heights = [None] * 5
            # fill heights except index 2
            for idx, h in zip(fill_indices, perm_heights):
                heights[idx] = h
            heights[fixed_house_index] = fixed_height

            # Clue 1: Alice is short
            if heights[names.index("Alice")] != "short":
                continue

            # Clue 3: average not in second house (index 1)
            if heights[1] == "average":
                continue

            # Clue 10: very short left of Arnold
            if not (heights.index("very short") < idx_arnold):
                continue

            # Foods: fix pizza at house 3
            other_foods = [f for f in foods_all if f != fixed_food]
            for perm_foods in itertools.permutations(other_foods):
                foods = [None] * 5
                for idx, f in zip(fill_indices, perm_foods):
                    foods[idx] = f
                foods[fixed_house_index] = fixed_food

                # Clue 5: stir fry is Arnold's food
                if foods[idx_arnold] != "stir fry":
                    continue

                # Clue 9: grilled cheese right of Eric (house 3 index 2)
                if not (foods.index("grilled cheese") > names.index("Eric")):
                    continue

                # Clue 6: pizza lover is tall (already ensured by fixing both at index 2)
                if foods.index("pizza") != heights.index("tall"):
                    continue

                # Clue 4: average left of stew
                if not (heights.index("average") < foods.index("stew")):
                    continue

                # All constraints satisfied
                solutions.append((names, heights, foods))

    # Choose the first solution (should be unique)
    if not solutions:
        raise RuntimeError("No solution found.")
    names, heights, foods = solutions[0]

    result = {
        "solution": {
            "header": ["House", "Name", "Height", "Food"],
            "rows": [
                [str(i + 1), names[i], heights[i], foods[i]] for i in range(5)
            ]
        }
    }
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))