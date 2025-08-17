import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]
    names = ["Peter", "Alice", "Eric", "Bob", "Arnold"]
    birthdays = ["april", "feb", "mar", "jan", "sept"]
    cigars = ["pall mall", "prince", "dunhill", "blends", "blue master"]
    drinks = ["water", "coffee", "tea", "milk", "root beer"]

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for birthday_perm in itertools.permutations(birthdays):
            for cigar_perm in itertools.permutations(cigars):
                for drink_perm in itertools.permutations(drinks):
                    # Create a dictionary for easy access
                    house_dict = {house: {"name": name, "birthday": birthday, "cigar": cigar, "drink": drink}
                                  for house, (name, birthday, cigar, drink) in zip(houses, zip(name_perm, birthday_perm, cigar_perm, drink_perm))}

                    # Check constraints
                    if (house_dict[3]["name"] == "Eric" and  # Clue 13
                        house_dict[3]["cigar"] == "pall mall" and  # Clue 2
                        house_dict[birthday_perm.index("april") + 1]["name"] == "Bob" and  # Clue 3
                        house_dict[birthday_perm.index("mar") + 1]["cigar"] == "dunhill" and  # Clue 4
                        name_perm.index("Eric") < name_perm.index("Peter") and  # Clue 5
                        abs(name_perm.index("Peter") - birthday_perm.index("jan") - 1) == 1 and  # Clue 6
                        birthday_perm.index("feb") + 1 == 2 and  # Clue 8
                        house_dict[birthday_perm.index("feb") + 1]["cigar"] == "blends" and  # Clue 7
                        name_perm.index("Arnold") + 1 == name_perm.index("Peter") and  # Clue 9
                        drink_perm[4] != "milk" and  # Clue 10
                        house_dict[cigar_perm.index("blue master") + 1]["drink"] == "coffee" and  # Clue 11
                        abs(drink_perm.index("tea") - drink_perm.index("coffee")) == 2):  # Clue 12

                        # Prepare the solution in the required format
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Birthday", "Cigar", "Drink"],
                                "rows": [[str(house), house_dict[house]["name"], house_dict[house]["birthday"], house_dict[house]["cigar"], house_dict[house]["drink"]] for house in houses]
                            }
                        }

                        # Output the solution as JSON
                        print(json.dumps(solution))
                        return

solve_puzzle()