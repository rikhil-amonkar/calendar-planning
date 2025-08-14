#!/usr/bin/env python3
import itertools
import json

def main():
    names_all = ["Arnold", "Peter", "Eric", "Alice", "Bob"]
    hobbies_all = ["painting", "cooking", "knitting", "gardening", "photography"]
    heights_all = ["very tall", "tall", "very short", "average", "short"]
    lunches_all = ["stew", "grilled cheese", "stir fry", "spaghetti", "pizza"]

    solution_found = None

    # Iterate over permutations of names
    for names in itertools.permutations(names_all):
        # Clue 3: Peter is not in the second house (house index 1)
        if names[1] == "Peter":
            continue
        # Clue 8: Eric is not in the fifth house (house index 4)
        if names[4] == "Eric":
            continue
        # Clue 14: Alice is somewhere to the right of the photography enthusiast.
        # Since Bob is the photography enthusiast (Clue 1), find the positions of Bob and Alice.
        try:
            pos_bob = names.index("Bob")
            pos_alice = names.index("Alice")
        except ValueError:
            continue
        if pos_alice <= pos_bob:
            continue

        # Iterate over permutations of heights
        for heights in itertools.permutations(heights_all):
            # Clue 13: The person who is tall is in the third house (index 2)
            if heights[2] != "tall":
                continue
            # Clue 12: The person who is very short is in the fifth house (index 4)
            if heights[4] != "very short":
                continue
            # Clue 9: The person who is short is Peter.
            valid_heights = True
            for i in range(5):
                if names[i] == "Peter" and heights[i] != "short":
                    valid_heights = False
                    break
            if not valid_heights:
                continue

            # Iterate over permutations of hobbies
            for hobbies in itertools.permutations(hobbies_all):
                # Clue 11 (via its fixed form): The person who paints is directly left of the person with grilled cheese.
                # Clue 11 and Clue 2 force house2 to be painting, so check house2.
                if hobbies[1] != "painting":
                    continue
                # Clue 1: Bob is the photography enthusiast.
                valid_hobbies = True
                for i in range(5):
                    if names[i] == "Bob" and hobbies[i] != "photography":
                        valid_hobbies = False
                        break
                if not valid_hobbies:
                    continue

                # Iterate over permutations of lunches
                for lunches in itertools.permutations(lunches_all):
                    # Clue 2: The person who loves grilled cheese is the person who is tall.
                    # We already set house3 (index 2) to tall so force grilled cheese there.
                    if lunches[2] != "grilled cheese":
                        continue
                    # Clue 4: The person who is tall is directly left of the person who loves stir fry.
                    # With house3 being tall, house4 must be stir fry.
                    if lunches[3] != "stir fry":
                        continue
                    # Clue 7: The person who loves spaghetti (lunch spaghetti) is not in the second house.
                    if lunches[1] == "spaghetti":
                        continue

                    valid = True

                    # Clue 5: The person who loves cooking is the person who has an average height.
                    # This implies a one-to-one correspondence: if hobby is cooking then height is average and vice versa.
                    for i in range(5):
                        if hobbies[i] == "cooking" and heights[i] != "average":
                            valid = False
                            break
                        if heights[i] == "average" and hobbies[i] != "cooking":
                            valid = False
                            break
                    if not valid:
                        continue

                    # Clue 11: The person who paints as a hobby is directly left of the person who loves eating grilled cheese.
                    for i in range(5):
                        if hobbies[i] == "painting":
                            if i == 4 or lunches[i+1] != "grilled cheese":
                                valid = False
                                break
                    if not valid:
                        continue

                    # Clue 6: Alice is directly left of the person who is a pizza lover.
                    for i in range(5):
                        if names[i] == "Alice":
                            if i == 4 or lunches[i+1] != "pizza":
                                valid = False
                                break
                    if not valid:
                        continue

                    # Clue 10: The person who has an average height and the person who enjoys gardening are next to each other.
                    avg_index = None
                    for i in range(5):
                        if heights[i] == "average":
                            avg_index = i
                            break
                    if avg_index is None:
                        valid = False
                    else:
                        neighbor_garden = False
                        if avg_index > 0 and hobbies[avg_index - 1] == "gardening":
                            neighbor_garden = True
                        if avg_index < 4 and hobbies[avg_index + 1] == "gardening":
                            neighbor_garden = True
                        if not neighbor_garden:
                            valid = False
                    if not valid:
                        continue

                    # Clue 4 re-check: The person who is tall is directly left of the person who loves stir fry.
                    for i in range(5):
                        if heights[i] == "tall":
                            if i == 4 or lunches[i+1] != "stir fry":
                                valid = False
                                break
                    if not valid:
                        continue

                    # All constraints have been satisfied; record the solution.
                    sol = []
                    # Houses are numbered as strings from "1" to "5" and order is left to right.
                    for i in range(5):
                        sol.append([str(i+1), names[i], hobbies[i], heights[i], lunches[i]])
                    solution_found = sol
                    break
                if solution_found is not None:
                    break
            if solution_found is not None:
                break
        if solution_found is not None:
            break

    result = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Height", "Lunch"],
            "rows": solution_found if solution_found is not None else []
        }
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()