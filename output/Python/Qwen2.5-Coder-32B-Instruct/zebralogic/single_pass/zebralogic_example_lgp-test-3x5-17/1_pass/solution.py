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

    # Function to check if a permutation satisfies all the clues
    def is_valid_solution(names_perm, phones_perm, heights_perm, house_styles_perm, car_models_perm):
        # Unpack the permutations into lists for easier access
        n1, n2, n3 = names_perm
        p1, p2, p3 = phones_perm
        h1, h2, h3 = heights_perm
        hs1, hs2, hs3 = house_styles_perm
        cm1, cm2, cm3 = car_models_perm

        # Check each clue
        if not (n2 == "Arnold"): return False
        if not (hs2 == "colonial"): return False
        if not (h1 == "average"): return False
        if not (hs2 == "colonial" and hs1 == "ranch"): return False
        if not (h1 == "very short" and cm1 == "tesla model 3"): return False
        if not (h3 == "short" and p3 == "samsung galaxy s21"): return False
        if not (p1 == "iphone 13" and p2 == "google pixel 6"): return False
        if not (cm2 == "toyota camry" and cm3 == "ford f150"): return False
        if not (names.index("Peter") > names.index("Eric")): return False

        return True

    # Iterate over all permutations to find the valid solution
    for names_perm in itertools.permutations(names):
        for phones_perm in itertools.permutations(phones):
            for heights_perm in itertools.permutations(heights):
                for house_styles_perm in itertools.permutations(house_styles):
                    for car_models_perm in itertools.permutations(car_models):
                        if is_valid_solution(names_perm, phones_perm, heights_perm, house_styles_perm, car_models_perm):
                            # Construct the solution in the required format
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
                            return json.dumps(solution)

# Print the solution as JSON
print(solve_puzzle())