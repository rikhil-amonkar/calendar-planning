import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ['Eric', 'Peter', 'Arnold']
    drinks = ['tea', 'water', 'milk']
    nationalities = ['dane', 'brit', 'swede']
    educations = ['high school', 'associate', 'bachelor']
    house_styles = ['victorian', 'colonial', 'ranch']
    smoothies = ['cherry', 'watermelon', 'desert']

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(names)) + \
                       list(itertools.permutations(drinks)) + \
                       list(itertools.permutations(nationalities)) + \
                       list(itertools.permutations(educations)) + \
                       list(itertools.permutations(house_styles)) + \
                       list(itertools.permutations(smoothies))

    # Check all combinations of permutations
    for names_perm, drinks_perm, nationalities_perm, educations_perm, house_styles_perm, smoothies_perm in itertools.product(all_permutations, repeat=6):
        # Unpack the permutations into separate lists
        name1, name2, name3 = names_perm
        drink1, drink2, drink3 = drinks_perm
        nationality1, nationality2, nationality3 = nationalities_perm
        education1, education2, education3 = educations_perm
        house_style1, house_style2, house_style3 = house_styles_perm
        smoothie1, smoothie2, smoothie3 = smoothies_perm

        # Create a list of dictionaries for each house
        houses = [
            {"name": name1, "drink": drink1, "nationality": nationality1, "education": education1, "house_style": house_style1, "smoothie": smoothie1},
            {"name": name2, "drink": drink2, "nationality": nationality2, "education": education2, "house_style": house_style2, "smoothie": smoothie2},
            {"name": name3, "drink": drink3, "nationality": nationality3, "education": education3, "house_style": house_style3, "smoothie": smoothie3}
        ]

        # Check all the clues
        if (abs(houses.index(next(house for house in houses if house["name"] == "Eric")) -
                houses.index(next(house for house in houses if house["drink"] == "tea"))) == 2 and
            next(house for house in houses if house["drink"] == "milk")["house_style"] == "ranch" and
            houses[1]["education"] == "bachelor" and
            next(house for house in houses if house["education"] == "high school")["nationality"] == "dane" and
            next(house for house in houses if house["smoothie"] == "desert")["nationality"] == "swede" and
            houses[0]["house_style"] != "victorian" and
            next(house for house in houses if house["smoothie"] == "cherry")["house_style"] == "colonial" and
            houses.index(next(house for house in houses if house["house_style"] == "victorian")) < houses.index(next(house for house in houses if house["name"] == "Arnold")) and
            next(house for house in houses if house["house_style"] == "ranch")["education"] == "high school"):
            # If all clues are satisfied, format the solution
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
            return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())