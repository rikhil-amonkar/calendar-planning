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

    # Iterate through all permutations to find the correct one
    for names_perm, drinks_perm, vacations_perm, house_styles_perm, animals_perm, birthdays_perm in all_permutations:
        # Unpack the permutations into variables for easier access
        name1, name2, name3 = names_perm
        drink1, drink2, drink3 = drinks_perm
        vacation1, vacation2, vacation3 = vacations_perm
        house_style1, house_style2, house_style3 = house_styles_perm
        animal1, animal2, animal3 = animals_perm
        birthday1, birthday2, birthday3 = birthdays_perm

        # Apply the clues to filter out incorrect permutations
        if (house_styles.index("colonial") < drinks.index("milk") and
            vacations.index("city") == house_styles.index("victorian") - 1 and
            birthdays.index("jan") == animals.index("cat") - 1 and
            drinks.index("water") == vacations.index("mountain") and
            animals.index("horse") == names.index("Peter") and
            house_styles.index("victorian") > vacations.index("beach") and
            vacations.index("city") == names.index("Peter") and
            vacations.index("mountain") == birthdays.index("april") and
            drinks.index("water") == names.index("Eric")):

            # Construct the solution in the required format
            solution = {
                "solution": {
                    "header": ["House", "Name", "Drink", "Vacation", "HouseStyle", "Animal", "Birthday"],
                    "rows": [
                        ["1", name1, drink1, vacation1, house_style1, animal1, birthday1],
                        ["2", name2, drink2, vacation2, house_style2, animal2, birthday2],
                        ["3", name3, drink3, vacation3, house_style3, animal3, birthday3]
                    ]
                }
            }

            # Output the solution as a JSON string
            print(json.dumps(solution, indent=2))
            return

# Call the function to solve the puzzle
solve_puzzle()