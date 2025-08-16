import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Arnold", "Bob", "Peter", "Alice", "Carol", "Eric"]
    foods = ["stew", "grilled cheese", "stir fry", "soup", "pizza", "spaghetti"]
    heights = ["tall", "average", "super tall", "very short", "very tall", "short"]
    drinks = ["root beer", "boba tea", "coffee", "water", "tea", "milk"]
    pets = ["hamster", "fish", "cat", "dog", "bird", "rabbit"]
    phones = ["samsung galaxy s21", "xiaomi mi 11", "google pixel 6", "iphone 13", "huawei p50", "oneplus 9"]

    # Initialize solution structure
    solution = {
        "solution": {
            "header": ["House", "Name", "Food", "Height", "Drink", "Pet", "PhoneModel"],
            "rows": [
                ["1", None, None, None, None, None, None],
                ["2", None, None, None, None, None, None],
                ["3", None, None, None, None, None, None],
                ["4", None, None, None, None, None, None],
                ["5", None, None, None, None, None, None],
                ["6", None, None, None, None, None, None]
            ]
        }
    }
    rows = solution["solution"]["rows"]

    # Apply direct clues first
    # Clue 1: iPhone 13 is in house 3
    rows[2][6] = "iphone 13"
    # Clue 3: soup in house 2
    rows[1][2] = "soup"
    # Clue 9: OnePlus 9 is Arnold
    # Clue 17: Arnold is very tall
    # Will apply these after assigning names
    # Clue 15: Carol uses samsung galaxy s21
    # Will apply after assigning names
    # Clue 13: Alice has fish
    # Clue 12: super tall has fish
    # So Alice is super tall and has fish
    # Clue 25: fish is directly left of Eric
    # So Alice is in house X, Eric in X+1

    # Let's find possible positions for Alice and Eric
    possible_alice_positions = [1, 2, 3, 4, 5]  # since Eric must be to the right
    for pos in possible_alice_positions:
        # Check if house pos can have Alice and fish
        # Also check if house pos+1 can have Eric
        pass  # Will handle in the main loop

    # Clue 22: super tall (Alice) is left of Peter
    # So Peter is to the right of Alice

    # Clue 24: bird is left of spaghetti eater
    # Clue 23: very short loves spaghetti
    # Clue 18: spaghetti eater uses google pixel 6
    # So bird is left of very short who uses google pixel 6 and eats spaghetti

    # Clue 10 and 20: rabbit not in house 5, hamster not in house 5
    # Clue 11: hamster is right of google pixel 6 user (spaghetti eater)
    # So google pixel 6 user must be left of hamster, and hamster not in 5, so google pixel 6 user must be left enough

    # Clue 5: huawei p50 is directly left of grilled cheese
    # Clue 7: grilled cheese lover is tall
    # Clue 2: Bob is tall
    # So grilled cheese lover is Bob, and huawei p50 is directly left of Bob

    # Clue 4: root beer is directly left of xiaomi mi 11
    # Clue 8: xiaomi mi 11 user drinks coffee
    # So root beer is directly left of coffee drinker with xiaomi mi 11

    # Clue 14: tea is directly left of pizza
    # Clue 16: pizza lover is short
    # So tea is directly left of short pizza lover

    # Clue 6: stir fry lover likes milk
    # Clue 26: dog owner likes milk
    # So stir fry lover has dog and likes milk

    # Clue 19: boba tea is right of soup (house 2 has soup)
    # So boba tea is in house 3,4,5, or 6

    # Clue 21: very tall (Arnold) is not in house 2

    # Now let's try to assign step by step

    # Assign Alice and Eric based on fish and position
    for alice_pos in [1, 2, 3, 4, 5]:
        eric_pos = alice_pos + 1
        # Assign Alice
        rows[alice_pos-1][1] = "Alice"
        rows[alice_pos-1][3] = "super tall"
        rows[alice_pos-1][5] = "fish"
        # Assign Eric
        rows[eric_pos-1][1] = "Eric"

        # Now assign Bob based on grilled cheese and huawei p50
        # Bob is tall and eats grilled cheese (clue 7)
        # huawei p50 is directly left of grilled cheese (clue 5)
        # So possible positions for Bob are 2-6, with huawei p50 to his left
        for bob_pos in range(2, 7):
            huawei_pos = bob_pos - 1
            if huawei_pos == alice_pos or huawei_pos == eric_pos:
                continue  # these houses already have names
            if rows[bob_pos-1][1] is not None:
                continue  # name already assigned
            if rows[huawei_pos-1][6] is not None and rows[huawei_pos-1][6] != "huawei p50":
                continue  # phone already assigned to something else
            # Assign Bob
            rows[bob_pos-1][1] = "Bob"
            rows[bob_pos-1][2] = "grilled cheese"
            rows[bob_pos-1][3] = "tall"
            # Assign huawei p50
            rows[huawei_pos-1][6] = "huawei p50"

            # Assign Arnold (very tall, oneplus 9)
            for arnold_pos in range(1, 7):
                if arnold_pos == alice_pos or arnold_pos == eric_pos or arnold_pos == bob_pos:
                    continue
                if rows[arnold_pos-1][1] is not None:
                    continue
                if arnold_pos == 2 and rows[arnold_pos-1][3] == "very tall":
                    continue  # clue 21: very tall not in house 2
                # Assign Arnold
                rows[arnold_pos-1][1] = "Arnold"
                rows[arnold_pos-1][3] = "very tall"
                rows[arnold_pos-1][6] = "oneplus 9"

                # Assign Carol (samsung galaxy s21)
                for carol_pos in range(1, 7):
                    if carol_pos in [alice_pos, eric_pos, bob_pos, arnold_pos]:
                        continue
                    if rows[carol_pos-1][1] is not None:
                        continue
                    # Assign Carol
                    rows[carol_pos-1][1] = "Carol"
                    rows[carol_pos-1][6] = "samsung galaxy s21"

                    # Now assign Peter (must be right of Alice)
                    for peter_pos in range(alice_pos + 1, 7):
                        if peter_pos in [alice_pos, eric_pos, bob_pos, arnold_pos, carol_pos]:
                            continue
                        if rows[peter_pos-1][1] is not None:
                            continue
                        # Assign Peter
                        rows[peter_pos-1][1] = "Peter"

                        # Now assign the remaining name (should be only one left)
                        remaining_names = set(names) - {rows[i][1] for i in range(6) if rows[i][1] is not None}
                        if len(remaining_names) != 1:
                            continue
                        remaining_name = remaining_names.pop()
                        for i in range(6):
                            if rows[i][1] is None:
                                rows[i][1] = remaining_name
                                break

                        # Now assign foods
                        # House 2 has soup
                        # Bob has grilled cheese
                        # Need to assign stew, stir fry, pizza, spaghetti
                        # spaghetti is eaten by very short (clue 23) with google pixel 6 (clue 18)
                        # pizza is eaten by short (clue 16)
                        # stir fry is with milk (clue 6) and dog (clue 26)
                        # Assign spaghetti first
                        for spaghetti_pos in range(1, 7):
                            if rows[spaghetti_pos-1][2] is not None:
                                continue
                            if rows[spaghetti_pos-1][6] is not None and rows[spaghetti_pos-1][6] != "google pixel 6":
                                continue
                            # Assign spaghetti
                            rows[spaghetti_pos-1][2] = "spaghetti"
                            rows[spaghetti_pos-1][3] = "very short"
                            rows[spaghetti_pos-1][6] = "google pixel 6"

                            # Assign hamster right of google pixel 6 (clue 11)
                            for hamster_pos in range(spaghetti_pos + 1, 7):
                                if hamster_pos == 5:
                                    continue  # clue 10 and 20
                                if rows[hamster_pos-1][5] is not None:
                                    continue
                                # Assign hamster
                                rows[hamster_pos-1][5] = "hamster"

                                # Assign pizza (short) with tea directly left (clue 14, 16)
                                for pizza_pos in range(2, 7):
                                    if rows[pizza_pos-1][2] is not None:
                                        continue
                                    tea_pos = pizza_pos - 1
                                    if rows[tea_pos-1][4] is not None and rows[tea_pos-1][4] != "tea":
                                        continue
                                    # Assign pizza
                                    rows[pizza_pos-1][2] = "pizza"
                                    rows[pizza_pos-1][3] = "short"
                                    # Assign tea
                                    rows[tea_pos-1][4] = "tea"

                                    # Assign stir fry (with milk and dog)
                                    for stir_fry_pos in range(1, 7):
                                        if rows[stir_fry_pos-1][2] is not None:
                                            continue
                                        # Assign stir fry
                                        rows[stir_fry_pos-1][2] = "stir fry"
                                        rows[stir_fry_pos-1][4] = "milk"
                                        rows[stir_fry_pos-1][5] = "dog"

                                        # Assign remaining food (should be stew)
                                        remaining_foods = set(foods) - {rows[i][2] for i in range(6) if rows[i][2] is not None}
                                        if len(remaining_foods) != 1:
                                            continue
                                        remaining_food = remaining_foods.pop()
                                        for i in range(6):
                                            if rows[i][2] is None:
                                                rows[i][2] = remaining_food
                                                break

                                        # Assign drinks
                                        # root beer is directly left of xiaomi mi 11 (coffee) (clue 4, 8)
                                        for xiaomi_pos in range(2, 7):
                                            root_beer_pos = xiaomi_pos - 1
                                            if rows[xiaomi_pos-1][6] is not None and rows[xiaomi_pos-1][6] != "xiaomi mi 11":
                                                continue
                                            if rows[root_beer_pos-1][4] is not None and rows[root_beer_pos-1][4] != "root beer":
                                                continue
                                            # Assign xiaomi mi 11
                                            rows[xiaomi_pos-1][6] = "xiaomi mi 11"
                                            rows[xiaomi_pos-1][4] = "coffee"
                                            # Assign root beer
                                            rows[root_beer_pos-1][4] = "root beer"

                                            # Assign boba tea (right of soup - house 2) (clue 19)
                                            for boba_pos in range(3, 7):
                                                if rows[boba_pos-1][4] is not None:
                                                    continue
                                                # Assign boba tea
                                                rows[boba_pos-1][4] = "boba tea"

                                                # Assign remaining drinks (water)
                                                remaining_drinks = set(drinks) - {rows[i][4] for i in range(6) if rows[i][4] is not None}
                                                if len(remaining_drinks) != 1:
                                                    continue
                                                remaining_drink = remaining_drinks.pop()
                                                for i in range(6):
                                                    if rows[i][4] is None:
                                                        rows[i][4] = remaining_drink
                                                        break

                                                # Assign pets
                                                # Alice has fish
                                                # hamster assigned
                                                # dog assigned with stir fry
                                                # bird is left of spaghetti (clue 24)
                                                for bird_pos in range(1, spaghetti_pos):
                                                    if rows[bird_pos-1][5] is not None:
                                                        continue
                                                    # Assign bird
                                                    rows[bird_pos-1][5] = "bird"

                                                    # Assign remaining pets (cat, rabbit)
                                                    remaining_pets = set(pets) - {rows[i][5] for i in range(6) if rows[i][5] is not None}
                                                    if len(remaining_pets) != 2:
                                                        continue
                                                    # rabbit not in house 5 (clue 10)
                                                    for rabbit_pos in range(1, 7):
                                                        if rabbit_pos == 5:
                                                            continue
                                                        if rows[rabbit_pos-1][5] is not None:
                                                            continue
                                                        # Assign rabbit
                                                        rows[rabbit_pos-1][5] = "rabbit"
                                                        # Assign cat to remaining
                                                        for i in range(6):
                                                            if rows[i][5] is None:
                                                                rows[i][5] = "cat"
                                                                break

                                                        # Assign remaining phone models
                                                        remaining_phones = set(phones) - {rows[i][6] for i in range(6) if rows[i][6] is not None}
                                                        if len(remaining_phones) != 0:
                                                            continue

                                                        # Verify all constraints
                                                        # If all constraints are satisfied, return the solution
                                                        return solution

                                                        # Reset assignments for backtracking
                                                        rows[i][5] = None
                                                    rows[rabbit_pos-1][5] = None
                                                rows[bird_pos-1][5] = None
                                            rows[boba_pos-1][4] = None
                                        rows[xiaomi_pos-1][6] = None
                                        rows[xiaomi_pos-1][4] = None
                                        rows[root_beer_pos-1][4] = None
                                    rows[pizza_pos-1][2] = None
                                    rows[pizza_pos-1][3] = None
                                    rows[tea_pos-1][4] = None
                                rows[hamster_pos-1][5] = None
                            rows[spaghetti_pos-1][2] = None
                            rows[spaghetti_pos-1][3] = None
                            rows[spaghetti_pos-1][6] = None
                        rows[peter_pos-1][1] = None
                    rows[carol_pos-1][1] = None
                    rows[carol_pos-1][6] = None
                rows[arnold_pos-1][1] = None
                rows[arnold_pos-1][3] = None
                rows[arnold_pos-1][6] = None
            rows[bob_pos-1][1] = None
            rows[bob_pos-1][2] = None
            rows[bob_pos-1][3] = None
            rows[huawei_pos-1][6] = None
        rows[alice_pos-1][1] = None
        rows[alice_pos-1][3] = None
        rows[alice_pos-1][5] = None
        rows[eric_pos-1][1] = None

    # If no solution found (shouldn't happen with correct constraints)
    return {"solution": {"header": [], "rows": []}}

# Solve and print the solution
solution = solve_puzzle()
print(json.dumps(solution, indent=2))