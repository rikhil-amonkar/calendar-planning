import itertools
import json

def solve_puzzle():
    # Define the attributes
    houses = [1, 2, 3, 4, 5]
    names = ["Peter", "Alice", "Eric", "Bob", "Arnold"]
    birthdays = ["april", "feb", "mar", "jan", "sept"]
    cigars = ["pall mall", "prince", "dunhill", "blends", "blue master"]
    drinks = ["water", "coffee", "tea", "milk", "root beer"]

    # Generate all possible permutations
    permutations = list(itertools.permutations(names))
    for perm in permutations:
        name_order = dict(zip(houses, perm))
        if name_order[3] != "Eric":
            continue

        permutations_birthday = list(itertools.permutations(birthdays))
        for perm_b in permutations_birthday:
            birthday_order = dict(zip(houses, perm_b))
            if birthday_order[3] != "April" or birthday_order[2] != "feb" or birthday_order[5] != "jan" or birthday_order[4] != "mar":
                continue

            permutations_cigar = list(itertools.permutations(cigars))
            for perm_c in permutations_cigar:
                cigar_order = dict(zip(houses, perm_c))
                if cigar_order[3] != "pall mall" or cigar_order[4] != "dunhill" or cigar_order[2] != "blends":
                    continue

                permutations_drink = list(itertools.permutations(drinks))
                for perm_d in permutations_drink:
                    drink_order = dict(zip(houses, perm_d))
                    if drink_order[2] != "milk" or drink_order[5] == "milk" or drink_order[name_order.index("Eric")] != "root beer" or drink_order[cigar_order.index("blue master")] != "coffee":
                        continue

                    # Check all remaining conditions
                    eric_house = name_order.index("Eric") + 1
                    if eric_house != 3:
                        continue

                    root_beer_lover_house = name_order.index("Eric") + 1
                    if not (name_order.index("Peter") > root_beer_lover_house):
                        continue

                    bob_house = birthday_order.index("April") + 1
                    if abs(name_order.index("Peter") - bob_house) != 1:
                        continue

                    jan_house = birthday_order.index("jan") + 1
                    if abs(name_order.index("Peter") - jan_house) != 1:
                        continue

                    feb_house = birthday_order.index("feb") + 1
                    if feb_house != 2:
                        continue

                    coffee_drinker_house = drink_order.index("coffee") + 1
                    tea_drinker_house = drink_order.index("tea") + 1
                    if abs(coffee_drinker_house - tea_drinker_house) != 1:
                        continue

                    arnold_house = name_order.index("Arnold") + 1
                    peter_house = name_order.index("Peter") + 1
                    if arnold_house != peter_house - 1:
                        continue

                    # If all conditions are satisfied, we have found the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Birthday", "Cigar", "Drink"],
                            "rows": []
                        }
                    }

                    for house in houses:
                        solution["solution"]["rows"].append([
                            str(house),
                            name_order[house],
                            birthday_order[house],
                            cigar_order[house],
                            drink_order[house]
                        ])

                    return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())