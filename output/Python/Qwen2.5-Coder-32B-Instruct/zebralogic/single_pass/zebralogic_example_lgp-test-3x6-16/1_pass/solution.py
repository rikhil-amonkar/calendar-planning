import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Eric", "Peter", "Arnold"]
    drinks = ["tea", "water", "milk"]
    nationalities = ["dane", "brit", "swede"]
    educations = ["high school", "associate", "bachelor"]
    house_styles = ["victorian", "colonial", "ranch"]
    smoothies = ["cherry", "watermelon", "desert"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(drinks)) * \
                       list(itertools.permutations(nationalities)) * \
                       list(itertools.permutations(educations)) * \
                       list(itertools.permutations(house_styles)) * \
                       list(itertools.permutations(smoothies))

    # Check each permutation against the clues
    for names_perm, drinks_perm, nationalities_perm, educations_perm, house_styles_perm, smoothies_perm in itertools.product(
        itertools.permutations(names),
        itertools.permutations(drinks),
        itertools.permutations(nationalities),
        itertools.permutations(educations),
        itertools.permutations(house_styles),
        itertools.permutations(smoothies)
    ):
        # Unpack the permutations into more readable variables
        name1, name2, name3 = names_perm
        drink1, drink2, drink3 = drinks_perm
        nationality1, nationality2, nationality3 = nationalities_perm
        education1, education2, education3 = educations_perm
        house_style1, house_style2, house_style3 = house_styles_perm
        smoothie1, smoothie2, smoothie3 = smoothies_perm

        # Apply the clues
        if abs(names.index("Eric") - drinks.index("tea")) != 1:
            continue
        if drinks.index("milk") != house_styles.index("ranch"):
            continue
        if educations[1] != "bachelor":
            continue
        if nationalities.index("dane") != educations.index("high school"):
            continue
        if nationalities.index("swede") != smoothies.index("desert"):
            continue
        if house_styles[0] == "victorian":
            continue
        if smoothies.index("cherry") != house_styles.index("colonial"):
            continue
        if house_styles.index("victorian") >= house_styles.index(name3):
            continue
        if house_styles.index("ranch") != educations.index("high school"):
            continue

        # If all clues are satisfied, construct the solution
        solution = {
            "solution": {
                "header": ["House", "Name", "Drink", "Nationality", "Education", "HouseStyle", "Smoothie"],
                "rows": [
                    ["1", name1, drink1, nationality1, education1, house_style1, smoothie1],
                    ["2", name2, drink2, nationality2, education2, house_style2, smoothie2],
                    ["3", name3, drink3, nationality3, education3, house_style3, smoothie3]
                ]
            }
        }

        # Output the solution as JSON
        print(json.dumps(solution))
        return

# Run the solver
solve_puzzle()