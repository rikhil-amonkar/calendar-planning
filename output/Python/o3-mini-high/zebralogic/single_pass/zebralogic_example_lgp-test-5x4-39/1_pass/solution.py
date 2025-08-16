#!/usr/bin/env python3
import itertools
import json

def main():
    # Define the fixed domains for each category.
    # Houses are indexed 0..4 corresponding to House1...House5.
    # Names available: 5 names.
    all_names = ["Arnold", "Peter", "Eric", "Alice", "Bob"]
    # We will fix "Alice" in one house because of clue 6.
    # From our reasoning, the only possibility is that "Alice" must be immediately left of the pizza lover.
    # That forces "Alice" to be in House4 (index 3) and House5's (index 4) food to be pizza.
    # So we fix:
    fixed_house_for_alice = 3

    # Hobbies available:
    all_hobbies = ["painting", "cooking", "knitting", "gardening", "photography"]
    # Clue: The person who paints is directly left of the person with grilled cheese.
    # We will fix "painting" in House2 (index 1) so that House3 gets "grilled cheese" food.
    fixed_house_for_painting = 1

    # Heights available:
    all_heights = ["very tall", "tall", "very short", "average", "short"]
    # Fixed constraints:
    # Clue 13: The person who is tall is in the third house -> index 2 must be "tall".
    # Clue 12: The person who is very short is in the fifth house -> index 4 must be "very short".
    fixed_height_index2 = "tall"
    fixed_height_index4 = "very short"

    # Foods available:
    all_foods = ["stew", "grilled cheese", "stir fry", "spaghetti", "pizza"]
    # From the clues, we can deduce many food positions:
    # Clue 2 and 13: House3 (index 2) gets "grilled cheese" (since the tall person loves grilled cheese).
    # Clue 4: The tall was directly left of stir fry -> House4 (index 3) gets "stir fry".
    # Clue 6: Alice is directly left of the pizza lover -> if Alice is in House4 (index 3) then House5 (index4) gets pizza.
    # The remaining two foods for House1 and House2: by elimination, they must be "spaghetti" and "stew".
    # Clue 7: The person who loves spaghetti is not in the second house -> So House2 (index1) cannot be spaghetti.
    # Hence, House1 (index0) gets "spaghetti" and House2 (index1) gets "stew".
    foods = [None] * 5
    foods[0] = "spaghetti"
    foods[1] = "stew"
    foods[2] = "grilled cheese"
    foods[3] = "stir fry"
    foods[4] = "pizza"

    # For the search, we will fix the positions that are already determined.
    # Names: Fix "Alice" in house index 3.
    # The remaining positions for names are indices 0, 1, 2, 4.
    remaining_names = [name for name in all_names if name != "Alice"]

    # Heights: Fixed positions: index 2 = "tall", index 4 = "very short".
    # Remaining indices: 0, 1, 3. They must take the remaining heights from all_heights
    # Remove "tall" and "very short".
    remaining_heights = [h for h in all_heights if h not in [fixed_height_index2, fixed_height_index4]]
    # That gives remaining_heights = ["very tall", "average", "short"]

    # Hobbies: Fixed: House2 (index 1) is "painting" (clue 11 forces that).
    # Remaining indices: 0, 2, 3, 4 must take the remaining hobbies.
    remaining_hobbies = [h for h in all_hobbies if h != "painting"]
    
    # Now iterate over permutations for names, heights, and hobbies.
    # Names: positions 0, 1, 2, 4 get a permutation of remaining_names.
    for names_perm in itertools.permutations(remaining_names):
        names = [None] * 5
        # assign according to our fixed positions:
        names[3] = "Alice"  # Fixed by our deduction.
        # The order for the remaining positions: indices 0,1,2,4.
        names[0] = names_perm[0]
        names[1] = names_perm[1]
        names[2] = names_perm[2]
        names[4] = names_perm[3]
        # Constraint: Clue 3: Peter is not in the second house (index 1)
        if names[1] == "Peter":
            continue
        # Constraint: Clue 8: Eric is not in the fifth house (index 4)
        if names[4] == "Eric":
            continue

        # Heights: positions 0,1,3 get a permutation of remaining_heights.
        for heights_perm in itertools.permutations(remaining_heights):
            heights = [None] * 5
            heights[0] = heights_perm[0]
            heights[1] = heights_perm[1]
            heights[2] = fixed_height_index2  # "tall" fixed for house3 (index2)
            heights[3] = heights_perm[2]
            heights[4] = fixed_height_index4  # "very short" fixed for house5

            # Constraint: Clue 9: The person who is short is Peter.
            # For every house: if height is "short", then name must be "Peter",
            # and if name is "Peter", then height must be "short".
            valid_peter = True
            for i in range(5):
                if heights[i] == "short" and names[i] != "Peter":
                    valid_peter = False
                    break
                if names[i] == "Peter" and heights[i] != "short":
                    valid_peter = False
                    break
            if not valid_peter:
                continue

            # Hobbies: positions 0,2,3,4 get a permutation of remaining_hobbies.
            for hobbies_perm in itertools.permutations(remaining_hobbies):
                hobbies = [None] * 5
                hobbies[1] = "painting"  # Fixed for house2 (index1)
                hobbies[0] = hobbies_perm[0]
                hobbies[2] = hobbies_perm[1]
                hobbies[3] = hobbies_perm[2]
                hobbies[4] = hobbies_perm[3]

                # Constraint: Clue 5: The person who loves cooking has an average height.
                # Interpret this as a bi-directional link: cooking <-> average.
                valid_cooking = True
                for i in range(5):
                    if hobbies[i] == "cooking" and heights[i] != "average":
                        valid_cooking = False
                        break
                    if heights[i] == "average" and hobbies[i] != "cooking":
                        valid_cooking = False
                        break
                if not valid_cooking:
                    continue
                    
                # Constraint: Clue 10: The person who has an average height and the person who enjoys gardening are next to each other.
                try:
                    avg_index = heights.index("average")
                except ValueError:
                    continue
                try:
                    garden_index = hobbies.index("gardening")
                except ValueError:
                    continue
                if abs(avg_index - garden_index) != 1:
                    continue

                # Constraint: Clue 14: Alice is somewhere to the right of the photography enthusiast.
                # That means the house with hobby "photography" must occur to the left of the house with name "Alice".
                try:
                    photo_index = hobbies.index("photography")
                except ValueError:
                    continue
                alice_index = names.index("Alice")
                if photo_index >= alice_index:
                    continue

                # Constraint: Clue 1: Bob is the photography enthusiast.
                # So if a house's name is "Bob", then its hobby must be "photography".
                valid_bob = True
                for i in range(5):
                    if names[i] == "Bob" and hobbies[i] != "photography":
                        valid_bob = False
                        break
                if not valid_bob:
                    continue

                # Constraint: Clue 11: The person who paints as a hobby is directly left of the person who loves eating grilled cheese.
                # Check for each house i (except the last) if hobby is painting then house (i+1) must have food "grilled cheese".
                valid_painting = True
                for i in range(4):
                    if hobbies[i] == "painting" and foods[i+1] != "grilled cheese":
                        valid_painting = False
                        break
                if not valid_painting:
                    continue

                # Constraint: Clue 2: The person who loves eating grilled cheese is the person who is tall.
                # This means for any house, if food is "grilled cheese" then height must be "tall", and vice versa.
                valid_grilled_cheese = True
                for i in range(5):
                    if foods[i] == "grilled cheese" and heights[i] != "tall":
                        valid_grilled_cheese = False
                        break
                    if heights[i] == "tall" and foods[i] != "grilled cheese":
                        valid_grilled_cheese = False
                        break
                if not valid_grilled_cheese:
                    continue

                # Constraint: Clue 4: The person who is tall is directly left of the person who loves stir fry.
                # Find the house with height "tall" and check the house immediately to its right.
                valid_stirfry = True
                try:
                    tall_index = heights.index("tall")
                except ValueError:
                    continue
                if tall_index < 4:
                    if foods[tall_index+1] != "stir fry":
                        valid_stirfry = False
                else:
                    valid_stirfry = False
                if not valid_stirfry:
                    continue

                # Constraint: Clue 6: Alice is directly left of the person who is a pizza lover.
                # Find the house with name "Alice" and check that the next house has food "pizza".
                valid_alice_pizza = True
                alice_pos = names.index("Alice")
                if alice_pos < 4:
                    if foods[alice_pos+1] != "pizza":
                        valid_alice_pizza = False
                else:
                    valid_alice_pizza = False
                if not valid_alice_pizza:
                    continue

                # Constraint: Clue 7 is automatically satisfied by our food assignment (House2 != spaghetti).

                # All constraints satisfied; we have found a solution.
                solution_rows = []
                header = ["House", "Name", "Hobby", "Height", "Food"]
                for i in range(5):
                    # House numbers are 1-indexed.
                    row = [str(i+1), names[i], hobbies[i], heights[i], foods[i]]
                    solution_rows.append(row)
                result = {
                    "solution": {
                        "header": header,
                        "rows": solution_rows
                    }
                }
                print(json.dumps(result, indent=2))
                return

if __name__ == "__main__":
    main()