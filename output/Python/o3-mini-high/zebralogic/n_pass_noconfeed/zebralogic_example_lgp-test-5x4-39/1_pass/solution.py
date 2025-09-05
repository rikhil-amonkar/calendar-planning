import itertools
import json

def valid_solution(names, hobbies, heights, foods):
    # Constraint 1: Bob is the photography enthusiast.
    for i in range(5):
        if names[i] == "Bob" and hobbies[i] != "photography":
            return False
        if hobbies[i] == "photography" and names[i] != "Bob":
            return False

    # Constraint 2: The person who loves grilled cheese is the person who is tall.
    for i in range(5):
        if foods[i] == "grilled cheese" and heights[i] != "tall":
            return False
        if heights[i] == "tall" and foods[i] != "grilled cheese":
            return False

    # Constraint 3: Peter is not in the second house.
    if names[1] == "Peter":
        return False

    # Constraint 4: The person who is tall is directly left of the person who loves stir fry.
    # (There is exactly one "tall" which must be directly left of "stir fry".)
    tall_index = None
    for i in range(5):
        if heights[i] == "tall":
            tall_index = i
    if tall_index is None or tall_index == 4 or foods[tall_index + 1] != "stir fry":
        return False

    # Constraint 5: The person who loves cooking is the person who has an average height.
    for i in range(5):
        if hobbies[i] == "cooking" and heights[i] != "average":
            return False
        if heights[i] == "average" and hobbies[i] != "cooking":
            return False

    # Constraint 6: Alice is directly left of the person who is a pizza lover.
    found_alice = False
    for i in range(5):
        if names[i] == "Alice":
            found_alice = True
            if i == 4 or foods[i + 1] != "pizza":
                return False
    if not found_alice:
        return False

    # Constraint 7: The person who loves spaghetti is not in the second house.
    if foods[1] == "spaghetti":
        return False

    # Constraint 8: Eric is not in the fifth house.
    if names[4] == "Eric":
        return False

    # Constraint 9: The person who is short is Peter.
    for i in range(5):
        if names[i] == "Peter" and heights[i] != "short":
            return False
        if heights[i] == "short" and names[i] != "Peter":
            return False

    # Constraint 10: The person who has an average height and the person who enjoys gardening are next to each other.
    avg_index = None
    garden_index = None
    for i in range(5):
        if heights[i] == "average":
            avg_index = i
        if hobbies[i] == "gardening":
            garden_index = i
    if avg_index is None or garden_index is None or abs(avg_index - garden_index) != 1:
        return False

    # Constraint 11: The person who paints as a hobby is directly left of the person who loves eating grilled cheese.
    found_painter = False
    for i in range(5):
        if hobbies[i] == "painting":
            found_painter = True
            if i == 4 or foods[i + 1] != "grilled cheese":
                return False
    if not found_painter:
        return False

    # Constraint 12: The person who is very short is in the fifth house.
    if heights[4] != "very short":
        return False

    # Constraint 13: The person who is tall is in the third house.
    if heights[2] != "tall":
        return False

    # Constraint 14: Alice is somewhere to the right of the photography enthusiast.
    alice_index = None
    photo_index = None
    for i in range(5):
        if names[i] == "Alice":
            alice_index = i
        if hobbies[i] == "photography":
            photo_index = i
    if alice_index is None or photo_index is None or alice_index <= photo_index:
        return False

    return True

def main():
    all_names = ["Arnold", "Peter", "Eric", "Alice", "Bob"]
    all_hobbies = ["painting", "cooking", "knitting", "gardening", "photography"]
    all_heights = ["very tall", "tall", "very short", "average", "short"]
    all_foods = ["stew", "grilled cheese", "stir fry", "spaghetti", "pizza"]

    solution_found = None

    # Iterate over permutations with early filtering for fixed positions.
    for perm_heights in itertools.permutations(all_heights):
        if perm_heights[2] != "tall" or perm_heights[4] != "very short":
            continue
        for perm_foods in itertools.permutations(all_foods):
            if perm_foods[2] != "grilled cheese" or perm_foods[3] != "stir fry":
                continue
            if perm_foods[1] == "spaghetti":
                continue
            for perm_hobbies in itertools.permutations(all_hobbies):
                if perm_hobbies[1] != "painting":
                    continue
                for perm_names in itertools.permutations(all_names):
                    if perm_names[1] == "Peter":
                        continue
                    if perm_names[4] == "Eric":
                        continue
                    if valid_solution(list(perm_names), list(perm_hobbies), list(perm_heights), list(perm_foods)):
                        solution_found = (list(perm_names), list(perm_hobbies), list(perm_heights), list(perm_foods))
                        break
                if solution_found:
                    break
            if solution_found:
                break
        if solution_found:
            break

    if solution_found:
        sol_names, sol_hobbies, sol_heights, sol_foods = solution_found
        result = {
            "solution": {
                "header": ["House", "Name", "Hobby", "Height", "Food"],
                "rows": [
                    [str(i + 1), sol_names[i], sol_hobbies[i], sol_heights[i], sol_foods[i]]
                    for i in range(5)
                ]
            }
        }
    else:
        result = {
            "solution": {
                "header": ["House", "Name", "Hobby", "Height", "Food"],
                "rows": []
            }
        }

    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()