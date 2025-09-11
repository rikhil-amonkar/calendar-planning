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
    names_perms = list(itertools.permutations(names))
    drinks_perms = list(itertools.permutations(drinks))
    vacations_perms = list(itertools.permutations(vacations))
    house_styles_perms = list(itertools.permutations(house_styles))
    animals_perms = list(itertools.permutations(animals))
    birthdays_perms = list(itertools.permutations(birthdays))

    # Generate the Cartesian product of all permutations
    all_combinations = itertools.product(
        names_perms,
        drinks_perms,
        vacations_perms,
        house_styles_perms,
        animals_perms,
        birthdays_perms
    )

    # Iterate through all combinations to find the correct one
    for names_perm, drinks_perm, vacations_perm, house_styles_perm, animals_perm, birthdays_perm in all_combinations:
        # Unpack the permutations into variables for easier access
        name1, name2, name3 = names_perm
        drink1, drink2, drink3 = drinks_perm
        vacation1, vacation2, vacation3 = vacations_perm
        house_style1, house_style2, house_style3 = house_styles_perm
        animal1, animal2, animal3 = animals_perm
        birthday1, birthday2, birthday3 = birthdays_perm

        # Apply the clues to filter out incorrect permutations
        if (house_styles_perm.index("colonial") < drinks_perm.index("milk") and
            vacations_perm.index("city") == house_styles_perm.index("victorian") - 1 and
            birthdays_perm.index("jan") == animals_perm.index("cat") - 1 and
            drinks_perm.index("water") == vacations_perm.index("mountain") and
            animals_perm.index("horse") == names_perm.index("Peter") and
            house_styles_perm.index("victorian") > vacations_perm.index("beach") and
            vacations_perm.index("city") == names_perm.index("Peter") and
            vacations_perm.index("mountain") == birthdays_perm.index("april") and
            drinks_perm.index("water") == names_perm.index("Eric")):

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