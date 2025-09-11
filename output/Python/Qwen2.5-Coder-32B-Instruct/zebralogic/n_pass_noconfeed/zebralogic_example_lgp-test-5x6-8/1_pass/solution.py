import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Eric", "Peter", "Arnold", "Bob", "Alice"]
    house_styles = ["modern", "craftsman", "ranch", "victorian", "colonial"]
    mothers = ["Penny", "Kailyn", "Holly", "Janelle", "Aniya"]
    phone_models = ["oneplus 9", "google pixel 6", "huawei p50", "iphone 13", "samsung galaxy s21"]
    drinks = ["coffee", "water", "root beer", "tea", "milk"]
    animals = ["fish", "dog", "horse", "bird", "cat"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(range(5)))

    # Iterate through all possible combinations
    for name_perm in all_permutations:
        for style_perm in all_permutations:
            for mother_perm in all_permutations:
                for phone_perm in all_permutations:
                    for drink_perm in all_permutations:
                        for animal_perm in all_permutations:
                            # Assign the permutations to the categories
                            name_map = {i: names[name_perm[i]] for i in range(5)}
                            style_map = {i: house_styles[style_perm[i]] for i in range(5)}
                            mother_map = {i: mothers[mother_perm[i]] for i in range(5)}
                            phone_map = {i: phone_models[phone_perm[i]] for i in range(5)}
                            drink_map = {i: drinks[drink_perm[i]] for i in range(5)}
                            animal_map = {i: animals[animal_perm[i]] for i in range(5)}

                            # Check the constraints
                            if (
                                # Constraint 1
                                phone_map[0] != "google pixel 6" and
                                # Constraint 2
                                drink_map[drink_perm.index(drinks.index("water"))] == "Alice" and
                                # Constraint 3
                                style_perm[style_perm.index(house_styles.index("colonial"))] > style_perm[phone_perm.index(phone_models.index("huawei p50"))] and
                                # Constraint 4
                                animal_map[animal_perm.index(animals.index("horse"))] == phone_map[phone_perm.index(phone_models.index("oneplus 9"))] and
                                # Constraint 5
                                style_map[style_perm.index(house_styles.index("ranch"))] == mother_map[mother_perm.index(mothers.index("Kailyn"))] and
                                # Constraint 6
                                drink_map[drink_perm.index(drinks.index("root beer"))] == animal_map[animal_perm.index(animals.index("cat"))] and
                                # Constraint 7
                                style_map[style_perm.index(house_styles.index("colonial"))] != 3 and
                                # Constraint 8
                                animal_map[3] == "bird" and
                                # Constraint 9
                                drink_map[drink_perm.index(drinks.index("tea"))] == "Bob" and
                                # Constraint 10
                                drink_perm[drink_perm.index(drinks.index("tea"))] > mother_perm[mother_perm.index(mothers.index("Kailyn"))] and
                                # Constraint 11
                                drink_perm[drink_perm.index(drinks.index("root beer"))] < mother_perm[mother_perm.index(mothers.index("Kailyn"))] and
                                # Constraint 12
                                animal_map[animal_perm.index(animals.index("horse"))] == style_map[style_perm.index(house_styles.index("modern"))] and
                                # Constraint 13
                                phone_map[phone_perm.index(phone_models.index("iphone 13"))] == drink_map[drink_perm.index(drinks.index("milk"))] and
                                # Constraint 14
                                animal_map[animal_perm.index(animals.index("dog"))] == drink_map[drink_perm.index(drinks.index("milk"))] and
                                # Constraint 15
                                phone_map[phone_perm.index(phone_models.index("google pixel 6"))] == style_map[style_perm.index(house_styles.index("craftsman"))] and
                                # Constraint 16
                                name_map[name_perm.index(names.index("Eric"))] != 1 and
                                # Constraint 17
                                drink_map[3] == "tea" and
                                # Constraint 18
                                animal_map[2] == "horse" and
                                # Constraint 19
                                style_map[style_perm.index(house_styles.index("modern"))] == mother_map[mother_perm.index(mothers.index("Penny"))] and
                                # Constraint 20
                                drink_map[drink_perm.index(drinks.index("root beer"))] == "Peter" and
                                # Constraint 21
                                mother_map[mother_perm.index(mothers.index("Aniya"))] != 3 and
                                # Constraint 22
                                mother_map[mother_perm.index(mothers.index("Janelle"))] == drink_map[drink_perm.index(drinks.index("water"))]
                            ):
                                # If all constraints are satisfied, construct the solution
                                solution = {
                                    "solution": {
                                        "header": ["House", "Name", "HouseStyle", "Mother", "PhoneModel", "Drink", "Animal"],
                                        "rows": [
                                            [str(i + 1), name_map[i], style_map[i], mother_map[i], phone_map[i], drink_map[i], animal_map[i]]
                                            for i in range(5)
                                        ]
                                    }
                                }
                                return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())