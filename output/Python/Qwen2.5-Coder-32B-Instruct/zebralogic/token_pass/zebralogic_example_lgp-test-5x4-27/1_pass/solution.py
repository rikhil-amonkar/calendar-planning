import itertools
import json

# Define the characteristics and their possible values
names = ["Peter", "Alice", "Eric", "Bob", "Arnold"]
birthdays = ["april", "feb", "mar", "jan", "sept"]
cigars = ["pall mall", "prince", "dunhill", "blends", "blue master"]
drinks = ["water", "coffee", "tea", "milk", "root beer"]

# Generate all possible permutations for the houses
permutations = list(itertools.permutations(range(5)))

# Function to check if a permutation satisfies all the clues
def is_valid_solution(house_names, house_birthdays, house_cigars, house_drinks):
    # Create mappings for easier checking
    name_to_house = {name: i for i, name in enumerate(house_names)}
    birthday_to_house = {birthday: i for i, birthday in enumerate(house_birthdays)}
    cigar_to_house = {cigar: i for i, cigar in enumerate(house_cigars)}
    drink_to_house = {drink: i for i, drink in enumerate(house_drinks)}

    # Check each clue
    if name_to_house["Eric"] != drink_to_house["root beer"]:
        return False
    if cigar_to_house["pall mall"] != 2:
        return False
    if name_to_house["Bob"] != birthday_to_house["april"]:
        return False
    if cigar_to_house["dunhill"] != birthday_to_house["mar"]:
        return False
    if name_to_house["Peter"] <= name_to_house["Eric"]:
        return False
    if abs(name_to_house["Peter"] - birthday_to_house["jan"]) != 1:
        return False
    if cigar_to_house["blends"] != birthday_to_house["feb"]:
        return False
    if birthday_to_house["feb"] != 1:
        return False
    if name_to_house["Arnold"] + 1 != name_to_house["Peter"]:
        return False
    if drink_to_house["milk"] == 4:
        return False
    if cigar_to_house["blue master"] != drink_to_house["coffee"]:
        return False
    if abs(drink_to_house["tea"] - drink_to_house["coffee"]) != 1:
        return False
    if name_to_house["Eric"] != 2:
        return False
    
    return True

# Iterate through all permutations to find a valid solution
for house_names in permutations:
    for house_birthdays in permutations:
        for house_cigars in permutations:
            for house_drinks in permutations:
                if is_valid_solution(house_names, house_birthdays, house_cigars, house_drinks):
                    # Format the solution as JSON
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Birthday", "Cigar", "Drink"],
                            "rows": [
                                [str(i+1), house_names[i], house_birthdays[i], house_cigars[i], house_drinks[i]]
                                for i in range(5)
                            ]
                        }
                    }
                    print(json.dumps(solution, indent=2))
                    exit()