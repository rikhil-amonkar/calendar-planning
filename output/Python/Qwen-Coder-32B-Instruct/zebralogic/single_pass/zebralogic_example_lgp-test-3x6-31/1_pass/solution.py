import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Eric", "Peter", "Arnold"]
    drinks = ["milk", "water", "tea"]
    vacations = ["mountain", "city", "beach"]
    house_styles = ["colonial", "victorian", "ranch"]
    animals = ["cat", "bird", "horse"]
    birthdays = ["jan", "sept", "april"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(drinks)) * \
                       list(itertools.permutations(vacations)) * \
                       list(itertools.permutations(house_styles)) * \
                       list(itertools.permutations(animals)) * \
                       list(itertools.permutations(birthdays))

    # Function to check if a given permutation satisfies all the clues
    def is_valid_solution(permutation):
        name_order, drink_order, vacation_order, house_style_order, animal_order, birthday_order = permutation

        # Unpack the permutations into individual variables for clarity
        name1, name2, name3 = name_order
        drink1, drink2, drink3 = drink_order
        vacation1, vacation2, vacation3 = vacation_order
        house_style1, house_style2, house_style3 = house_style_order
        animal1, animal2, animal3 = animal_order
        birthday1, birthday2, birthday3 = birthday_order

        # Check each clue
        if not (house_style_order.index("colonial") < drink_order.index("milk")):
            return False
        if not (vacation_order.index("city") == house_style_order.index("victorian") - 1):
            return False
        if not (birthday_order.index("jan") == animal_order.index("cat") - 1):
            return False
        if not (drink_order.index("water") == vacation_order.index("mountain")):
            return False
        if not (animal_order.index("horse") == names.index("Peter")):
            return False
        if not (house_style_order.index("victorian") > vacation_order.index("beach")):
            return False
        if not (names.index("Peter") == vacation_order.index("city")):
            return False
        if not (vacation_order.index("mountain") == birthday_order.index("april")):
            return False
        if not (names.index("Eric") == drink_order.index("water")):
            return False

        return True

    # Find the valid solution
    for permutation in all_permutations:
        if is_valid_solution(permutation):
            name_order, drink_order, vacation_order, house_style_order, animal_order, birthday_order = permutation
            solution = {
                "solution": {
                    "header": ["House", "Name", "Favorite Drink", "Vacation Preference", "House Style", "Animal", "Birthday Month"],
                    "rows": [
                        ["1", name_order[0], drink_order[0], vacation_order[0], house_style_order[0], animal_order[0], birthday_order[0]],
                        ["2", name_order[1], drink_order[1], vacation_order[1], house_style_order[1], animal_order[1], birthday_order[1]],
                        ["3", name_order[2], drink_order[2], vacation_order[2], house_style_order[2], animal_order[2], birthday_order[2]]
                    ]
                }
            }
            print(json.dumps(solution, indent=2))
            break

# Run the solver
solve_puzzle()