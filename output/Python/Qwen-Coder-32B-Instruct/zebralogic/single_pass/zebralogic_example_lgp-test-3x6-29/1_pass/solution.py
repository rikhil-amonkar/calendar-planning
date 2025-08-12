import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Arnold", "Peter", "Eric"]
    animals = ["bird", "horse", "cat"]
    birthdays = ["jan", "sept", "april"]
    hobbies = ["photography", "cooking", "gardening"]
    drinks = ["milk", "water", "tea"]
    hair_colors = ["black", "brown", "blonde"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(animals)) * \
                       list(itertools.permutations(birthdays)) * \
                       list(itertools.permutations(hobbies)) * \
                       list(itertools.permutations(drinks)) * \
                       list(itertools.permutations(hair_colors))

    # Check each permutation against the clues
    for names_perm, animals_perm, birthdays_perm, hobbies_perm, drinks_perm, hair_colors_perm in zip(
            itertools.permutations(names),
            itertools.permutations(animals),
            itertools.permutations(birthdays),
            itertools.permutations(hobbies),
            itertools.permutations(drinks),
            itertools.permutations(hair_colors)
    ):
        # Unpack the permutations into more readable variables
        name1, name2, name3 = names_perm
        animal1, animal2, animal3 = animals_perm
        birthday1, birthday2, birthday3 = birthdays_perm
        hobby1, hobby2, hobby3 = hobbies_perm
        drink1, drink2, drink3 = drinks_perm
        hair_color1, hair_color2, hair_color3 = hair_colors_perm

        # Apply the clues
        if (hair_color2 == "brown" and hobby2 == "cooking" and
            birthday3 == "april" and
            name1 != "Eric" and
            animal2 == "cat" and
            hair_colors.index("blonde") < drinks.index("milk") and
            hobby3 == "gardening" and drink3 == "milk" and
            animal2 == "cat" and hair_color2 == "brown" and
            name2 == "Arnold" and animal2 == "bird" and
            drink2 == "water" and hobby2 == "photography" and
            birthday2 == "sept" and name2 == "Arnold" and birthday1 == "jan"):
            # If all clues are satisfied, construct the solution
            solution = {
                "solution": {
                    "header": ["House", "Name", "Animal", "Birthday", "Hobby", "Drink", "Hair Color"],
                    "rows": [
                        ["1", name1, animal1, birthday1, hobby1, drink1, hair_color1],
                        ["2", name2, animal2, birthday2, hobby2, drink2, hair_color2],
                        ["3", name3, animal3, birthday3, hobby3, drink3, hair_color3]
                    ]
                }
            }
            return json.dumps(solution, indent=2)

# Run the function and print the result
print(solve_puzzle())