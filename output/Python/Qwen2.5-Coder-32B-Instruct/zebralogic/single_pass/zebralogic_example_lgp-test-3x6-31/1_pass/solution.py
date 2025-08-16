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

    # Function to check if a permutation satisfies all the clues
    def is_valid_solution(names, drinks, vacations, house_styles, animals, birthdays):
        # Unpack the permutations into lists
        n1, n2, n3 = names
        d1, d2, d3 = drinks
        v1, v2, v3 = vacations
        h1, h2, h3 = house_styles
        a1, a2, a3 = animals
        b1, b2, b3 = birthdays

        # Check each clue
        if not (h1 == "colonial" or (h1 == "victorian" and h2 == "colonial") or (h1 == "ranch" and h2 == "colonial")):
            return False
        if not (v1 == "city" and h2 == "victorian"):
            return False
        if not (b1 == "jan" and a2 == "cat"):
            return False
        if not (d2 == "water" and v2 == "mountain"):
            return False
        if not (a3 == "horse" and n3 == "Peter"):
            return False
        if not (h2 == "victorian" or h3 == "victorian" and v1 == "beach"):
            return False
        if not (n2 == "Peter" and v2 == "city"):
            return False
        if not (v3 == "mountain" and b3 == "april"):
            return False
        if not (n1 == "Eric" and d1 == "water"):
            return False

        return True

    # Iterate through all permutations to find the valid solution
    for names_perm in itertools.permutations(names):
        for drinks_perm in itertools.permutations(drinks):
            for vacations_perm in itertools.permutations(vacations):
                for house_styles_perm in itertools.permutations(house_styles):
                    for animals_perm in itertools.permutations(animals):
                        for birthdays_perm in itertools.permutations(birthdays):
                            if is_valid_solution(names_perm, drinks_perm, vacations_perm, house_styles_perm, animals_perm, birthdays_perm):
                                # Construct the solution in the required format
                                solution = {
                                    "solution": {
                                        "header": ["House", "Name", "Drink", "Vacation", "HouseStyle", "Animal", "Birthday"],
                                        "rows": [
                                            ["1", names_perm[0], drinks_perm[0], vacations_perm[0], house_styles_perm[0], animals_perm[0], birthdays_perm[0]],
                                            ["2", names_perm[1], drinks_perm[1], vacations_perm[1], house_styles_perm[1], animals_perm[1], birthdays_perm[1]],
                                            ["3", names_perm[2], drinks_perm[2], vacations_perm[2], house_styles_perm[2], animals_perm[2], birthdays_perm[2]]
                                        ]
                                    }
                                }
                                return json.dumps(solution, indent=2)

# Run the solver and print the result
print(solve_puzzle())