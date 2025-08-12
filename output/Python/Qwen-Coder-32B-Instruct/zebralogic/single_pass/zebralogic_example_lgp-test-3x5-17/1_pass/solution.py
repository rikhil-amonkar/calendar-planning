import itertools
import json

def solve_puzzle():
    # Define the possible values for each attribute
    names = ["Eric", "Arnold", "Peter"]
    phones = ["iphone 13", "samsung galaxy s21", "google pixel 6"]
    heights = ["very short", "average", "short"]
    house_styles = ["colonial", "ranch", "victorian"]
    cars = ["tesla model 3", "toyota camry", "ford f150"]

    # Generate all possible permutations for each attribute
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(phones)) * \
                       list(itertools.permutations(heights)) * \
                       list(itertools.permutations(house_styles)) * \
                       list(itertools.permutations(cars))

    # Check each permutation against the clues
    for names_perm, phones_perm, heights_perm, house_styles_perm, cars_perm in itertools.product(
        itertools.permutations(names),
        itertools.permutations(phones),
        itertools.permutations(heights),
        itertools.permutations(house_styles),
        itertools.permutations(cars)
    ):
        # Unpack the permutations for easier reference
        name1, name2, name3 = names_perm
        phone1, phone2, phone3 = phones_perm
        height1, height2, height3 = heights_perm
        house_style1, house_style2, house_style3 = house_styles_perm
        car1, car2, car3 = cars_perm

        # Apply the clues
        if (name2 == "Arnold" and
            house_style2 == "colonial" and
            height1 == "average" and
            house_style2 == "colonial" and house_style1 == "ranch" and
            name1 != name2 and name2 != name3 and name1 != name3 and
            phone1 != phone2 and phone2 != phone3 and phone1 != phone3 and
            height1 != height2 and height2 != height3 and height1 != height3 and
            house_style1 != house_style2 and house_style2 != house_style3 and house_style1 != house_style3 and
            car1 != car2 and car2 != car3 and car1 != car3 and
            names_perm.index("Peter") > names_perm.index("Eric") and
            heights_perm.index("very short") == cars_perm.index("tesla model 3") and
            heights_perm.index("short") + 1 == phones_perm.index("samsung galaxy s21") and
            phones_perm.index("iphone 13") + 1 == phones_perm.index("google pixel 6") and
            cars_perm.index("ford f150") > cars_perm.index("toyota camry")):

            # Construct the solution in the required format
            solution = {
                "solution": {
                    "header": ["House", "Name", "Phone Model", "Height", "House Style", "Car Model"],
                    "rows": [
                        ["1", name1, phone1, height1, house_style1, car1],
                        ["2", name2, phone2, height2, house_style2, car2],
                        ["3", name3, phone3, height3, house_style3, car3]
                    ]
                }
            }

            # Output the solution as JSON
            print(json.dumps(solution, indent=2))
            return

# Run the solver
solve_puzzle()