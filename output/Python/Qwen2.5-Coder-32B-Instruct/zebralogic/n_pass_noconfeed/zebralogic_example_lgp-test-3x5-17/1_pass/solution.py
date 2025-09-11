import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Eric", "Arnold", "Peter"]
    phones = ["iphone 13", "samsung galaxy s21", "google pixel 6"]
    heights = ["very short", "average", "short"]
    house_styles = ["colonial", "ranch", "victorian"]
    car_models = ["tesla model 3", "toyota camry", "ford f150"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(phones)) * \
                       list(itertools.permutations(heights)) * \
                       list(itertools.permutations(house_styles)) * \
                       list(itertools.permutations(car_models))

    # Function to check if a given permutation satisfies all the clues
    def is_valid_solution(names_perm, phones_perm, heights_perm, house_styles_perm, car_models_perm):
        # Unpack the permutations into separate lists for easier access
        name1, name2, name3 = names_perm
        phone1, phone2, phone3 = phones_perm
        height1, height2, height3 = heights_perm
        house_style1, house_style2, house_style3 = house_styles_perm
        car_model1, car_model2, car_model3 = car_models_perm

        # Apply each clue to check if the permutation is valid
        # Clue 1: Peter is somewhere to the right of Eric.
        if names.index("Peter") < names.index("Eric"):
            return False
        # Clue 2: The person living in a colonial-style house is in the second house.
        if house_style2 != "colonial":
            return False
        # Clue 3: The person who owns a Tesla Model 3 is the person who is very short.
        if car_models.index("tesla model 3") != heights.index("very short"):
            return False
        # Clue 4: The person who is short is directly left of the person who uses a Samsung Galaxy S21.
        if heights.index("short") + 1 == phones.index("samsung galaxy s21"):
            return False
        else:
            return True
        # Clue 5: The person who uses an iPhone 13 is directly left of the person who uses a Google Pixel 6.
        if phones.index("iphone 13") + 1 == phones.index("google pixel 6"):
            return False
        else:
            return True
        # Clue 6: The person living in a colonial-style house is somewhere to the right of the person in a ranch-style home.
        if house_styles.index("colonial") < house_styles.index("ranch"):
            return False
        # Clue 7: Arnold is in the second house.
        if names[1] != "Arnold":
            return False
        # Clue 8: The person who owns a Ford F-150 is somewhere to the right of the person who owns a Toyota Camry.
        if car_models.index("ford f150") < car_models.index("toyota camry"):
            return False
        # Clue 9: The person who has an average height is in the first house.
        if heights[0] != "average":
            return False

        return True

    # Iterate over all possible combinations of permutations
    for names_perm in itertools.permutations(names):
        for phones_perm in itertools.permutations(phones):
            for heights_perm in itertools.permutations(heights):
                for house_styles_perm in itertools.permutations(house_styles):
                    for car_models_perm in itertools.permutations(car_models):
                        if is_valid_solution(names_perm, phones_perm, heights_perm, house_styles_perm, car_models_perm):
                            # If a valid solution is found, format it as required
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "PhoneModel", "Height", "HouseStyle", "CarModel"],
                                    "rows": [
                                        ["1", names_perm[0], phones_perm[0], heights_perm[0], house_styles_perm[0], car_models_perm[0]],
                                        ["2", names_perm[1], phones_perm[1], heights_perm[1], house_styles_perm[1], car_models_perm[1]],
                                        ["3", names_perm[2], phones_perm[2], heights_perm[2], house_styles_perm[2], car_models_perm[2]]
                                    ]
                                }
                            }
                            # Print the solution as JSON
                            print(json.dumps(solution, indent=2))
                            return

# Run the function to solve the puzzle
solve_puzzle()