import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Peter", "Bob", "Carol", "Eric", "Alice", "Arnold"]
    pets = ["bird", "dog", "cat", "rabbit", "fish", "hamster"]
    house_styles = ["victorian", "ranch", "modern", "mediterranean", "colonial", "craftsman"]
    birthdays = ["mar", "sept", "may", "feb", "jan", "april"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(pets)) * \
                       list(itertools.permutations(house_styles)) * \
                       list(itertools.permutations(birthdays))

    # Function to check if a permutation satisfies all the clues
    def is_valid_solution(names_perm, pets_perm, house_styles_perm, birthdays_perm):
        # Unpack the permutations into more readable variables
        house1, house2, house3, house4, house5, house6 = range(6)

        # Clue 3 & 4
        if birthdays_perm[house2] != "may" or house_styles_perm[house2] != "colonial":
            return False

        # Clue 5
        if names_perm[house3] != "Carol":
            return False

        # Clue 7
        if pets_perm[house1] == "fish" and names_perm[house1] == "Bob":
            return False

        # Clue 8
        if names_perm[house6] != "Eric":
            return False

        # Clue 11 & 18
        if names_perm[house4] != "Arnold" or house_styles_perm[house4] != "craftsman":
            return False

        # Clue 14 & 17
        if names_perm[house2] != "Peter" or birthdays_perm[house3] != "mar":
            return False

        # Clue 19
        if pets_perm[house4] != "dog":
            return False

        # Clue 1
        if pets_perm.index("hamster") < birthdays_perm.index("mar"):
            return False

        # Clue 2
        if birthdays_perm.index("jan") > birthdays_perm.index("sept"):
            return False

        # Clue 6
        if house_styles_perm[house6] == "mediterranean":
            return False

        # Clue 9
        victorian_index = house_styles_perm.index("victorian")
        cat_index = pets_perm.index("cat")
        if abs(victorian_index - cat_index) != 1:
            return False

        # Clue 10
        hamster_index = pets_perm.index("hamster")
        if abs(victorian_index - hamster_index) != 2:
            return False

        # Clue 12
        if house_styles_perm.index("colonial") > house_styles_perm.index("modern"):
            return False

        # Clue 13
        if pets_perm[house2] == "fish":
            return False

        # Clue 15
        if birthdays_perm.index("jan") + 1 != birthdays_perm.index("april"):
            return False

        # Clue 16
        bird_index = pets_perm.index("bird")
        modern_index = house_styles_perm.index("modern")
        if abs(bird_index - modern_index) != 1:
            return False

        return True

    # Iterate over all permutations to find the valid solution
    for names_perm in itertools.permutations(names):
        for pets_perm in itertools.permutations(pets):
            for house_styles_perm in itertools.permutations(house_styles):
                for birthdays_perm in itertools.permutations(birthdays):
                    if is_valid_solution(names_perm, pets_perm, house_styles_perm, birthdays_perm):
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Pet", "HouseStyle", "Birthday"],
                                "rows": [
                                    [str(i + 1), names_perm[i], pets_perm[i], house_styles_perm[i], birthdays_perm[i]]
                                    for i in range(6)
                                ]
                            }
                        }
                        return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())