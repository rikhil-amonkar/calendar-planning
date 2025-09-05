#!/usr/bin/env python3
import itertools
import json

# The six possible values for each attribute.
names = ["Alice", "Arnold", "Peter", "Carol", "Bob", "Eric"]
birthdays = ["feb", "mar", "sept", "jan", "may", "april"]
foods = ["stew", "soup", "grilled cheese", "stir fry", "spaghetti", "pizza"]
# Use exactly these six heights.
heights = ["very short", "short", "average", "tall", "super tall", "very tall"]
cars = ["chevrolet silverado", "ford f150", "bmw 3 series", "tesla model 3", "toyota camry", "honda civic"]

# House numbers will be considered from 0 to 5 (corresponding to houses 1..6)

def valid(solution):
    # Unpack the solution: each is a tuple of 6 items (index 0 corresponds to house1, etc.)
    (names_sol, bdays, foods_sol, heights_sol, cars_sol) = solution

    # Helper: position of an item in an attribute list
    def pos(attr, value):
        return attr.index(value)  # returns the house-index where value is located

    # Constraint 1: The person who owns a Honda Civic is the person who is short.
    for i in range(6):
        if cars_sol[i] == "honda civic":
            if heights_sol[i] != "short":
                return False
    # Constraint 2: The person who owns a Ford F-150 is in the fifth house.
    if cars_sol[4] != "ford f150":
        return False
    # Constraint 3: The person who loves stir fry is somewhere to the left of Eric.
    try:
        idx_eric = names_sol.index("Eric")
    except ValueError:
        return False
    idx_stir = foods_sol.index("stir fry")
    if idx_stir >= idx_eric:
        return False
    # Constraint 4: The person whose birthday is in May is somewhere to the left of Carol.
    try:
        idx_may = bdays.index("may")
        idx_carol = names_sol.index("Carol")
    except ValueError:
        return False
    if idx_may >= idx_carol:
        return False
    # Constraint 5: The person who is very short is somewhere to the left of the person whose birthday is in April.
    try:
        idx_very_short = heights_sol.index("very short")
        idx_april = bdays.index("april")
    except ValueError:
        return False
    if idx_very_short >= idx_april:
        return False
    # Constraint 6: The person who owns a BMW 3 Series is not in the third house.
    if cars_sol[2] == "bmw 3 series":
        return False
    # Constraint 7: There are two houses between the person who loves stir fry and the person who is a pizza lover.
    idx_pizza = foods_sol.index("pizza")
    if abs(idx_pizza - idx_stir) != 3:
        return False
    # Constraint 8: The person who loves the soup is directly left of Eric.
    if idx_eric == 0 or foods_sol[idx_eric - 1] != "soup":
        return False
    # Constraint 9: The person who loves spaghetti and the person whose birthday is in May are next to each other.
    if abs(bdays.index("may") - foods_sol.index("spaghetti")) != 1:
        return False
    # Constraint 10: Alice is directly left of the person who owns a BMW 3 Series.
    try:
        idx_alice = names_sol.index("Alice")
        idx_bmw = cars_sol.index("bmw 3 series")
    except ValueError:
        return False
    if idx_alice == 5 or idx_alice + 1 != idx_bmw:
        return False
    # Constraint 11: The person who owns a Tesla Model 3 is somewhere to the left of the person who is tall.
    try:
        idx_tesla = cars_sol.index("tesla model 3")
        idx_tall = None
        # find house with height "tall" (exactly "tall")
        for i, h in enumerate(heights_sol):
            if h == "tall":
                idx_tall = i
                break
        if idx_tall is None or idx_tesla >= idx_tall:
            return False
    except ValueError:
        return False
    # Constraint 12: The person who is very tall is the person who owns a Toyota Camry.
    for i in range(6):
        if heights_sol[i] == "very tall":
            if cars_sol[i] != "toyota camry":
                return False
    # Constraint 13: Peter is directly left of the person who is a pizza lover.
    try:
        idx_peter = names_sol.index("Peter")
    except ValueError:
        return False
    if idx_peter == 5 or foods_sol[idx_peter + 1] != "pizza":
        return False
    # Constraint 14: The person who loves the stew is not in the third house.
    if foods_sol[2] == "stew":
        return False
    # Constraint 15: There is one house between the person whose birthday is in September and the person who is very short.
    try:
        idx_sept = bdays.index("sept")
    except ValueError:
        return False
    if abs(idx_sept - idx_very_short) != 2:
        return False
    # Constraint 16: There is one house between the person whose birthday is in March and the person who is super tall.
    try:
        idx_mar = bdays.index("mar")
    except ValueError:
        return False
    try:
        idx_super_tall = heights_sol.index("super tall")
    except ValueError:
        return False
    if abs(idx_super_tall - idx_mar) != 2:
        return False
    # Constraint 17: The person who is tall is Bob.
    try:
        if names_sol[heights_sol.index("tall")] != "Bob":
            return False
    except ValueError:
        return False
    # Constraint 18: The person whose birthday is in May is somewhere to the right of Alice.
    if bdays.index("may") <= names_sol.index("Alice"):
        return False
    # Constraint 19: The person who is very short is in the fourth house.
    if heights_sol[3] != "very short":
        return False
    # Constraint 20: The person whose birthday is in March is the person who is short.
    if bdays.index("mar") >= 0:
        idx = bdays.index("mar")
        if heights_sol[idx] != "short":
            return False
    # Constraint 21: Carol is the person who owns a Tesla Model 3.
    if names_sol.index("Carol") != cars_sol.index("tesla model 3"):
        return False
    # Constraint 22: Eric is the person whose birthday is in January.
    if bdays[names_sol.index("Eric")] != "jan":
        return False

    return True

# We'll iterate over all permutations for each category.
for perm_names in itertools.permutations(names):
    # Optimization: because of clues, we know "Alice" must be immediately left of BMW owner.
    # We'll generate all permutations for birthdays, foods, heights, cars.
    for perm_bdays in itertools.permutations(birthdays):
        for perm_foods in itertools.permutations(foods):
            for perm_heights in itertools.permutations(heights):
                # Clue 19: very short is in the 4th house (index 3)
                if perm_heights[3] != "very short":
                    continue
                for perm_cars in itertools.permutations(cars):
                    sol = (perm_names, perm_bdays, perm_foods, perm_heights, perm_cars)
                    if valid(sol):
                        # Build the output dictionary as required.
                        rows = []
                        for i in range(6):
                            row = [str(i+1),
                                   sol[0][i],
                                   sol[1][i],
                                   sol[2][i],
                                   sol[3][i],
                                   sol[4][i]]
                            rows.append(row)
                        output = {
                            "solution": {
                                "header": ["House", "Name", "Birthday", "Food", "Height", "CarModel"],
                                "rows": rows
                            }
                        }
                        print(json.dumps(output, indent=2))
                        exit(0)
                        
# If no solution found:
print(json.dumps({"solution": {"header": ["House", "Name", "Birthday", "Food", "Height", "CarModel"], "rows": []}}, indent=2))