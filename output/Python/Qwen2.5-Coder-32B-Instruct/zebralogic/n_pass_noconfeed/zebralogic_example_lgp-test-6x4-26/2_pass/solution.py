import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Peter", "Bob", "Carol", "Eric", "Alice", "Arnold"]
    pets = ["bird", "dog", "cat", "rabbit", "fish", "hamster"]
    house_styles = ["victorian", "ranch", "modern", "mediterranean", "colonial", "craftsman"]
    birthdays = ["mar", "sept", "may", "feb", "jan", "april"]

    # Generate all possible permutations
    all_permutations = list(itertools.permutations(range(6)))

    # Function to check if a permutation satisfies all the clues
    def is_valid(permutation):
        name_order = [names[i] for i in permutation]
        pet_order = [pets[i] for i in permutation]
        house_style_order = [house_styles[i] for i in permutation]
        birthday_order = [birthdays[i] for i in permutation]

        # Check clue 3 and 4
        if birthday_order[1] != "may" or house_style_order[1] != "colonial":
            return False

        # Check clue 5
        if name_order[2] != "Carol":
            return False

        # Check clue 7
        if name_order.index("Bob") > pet_order.index("fish"):
            return False

        # Check clue 8
        if name_order[5] != "Eric":
            return False

        # Check clue 9
        if abs(house_style_order.index("victorian") - pet_order.index("cat")) != 1:
            return False

        # Check clue 10
        if abs(house_style_order.index("victorian") - pet_order.index("hamster")) != 2:
            return False

        # Check clue 11 and 18
        if name_order[3] != "Arnold" or house_style_order[3] != "craftsman":
            return False

        # Check clue 12
        if house_style_order.index("colonial") > house_style_order.index("modern"):
            return False

        # Check clue 13
        if pet_order[1] == "fish":
            return False

        # Check clue 14
        if house_style_order[1] != "colonial" or name_order[1] != "Peter":
            return False

        # Check clue 15
        if birthday_order.index("jan") + 1 != birthday_order.index("april"):
            return False

        # Check clue 16
        if abs(house_style_order.index("modern") - pet_order.index("bird")) != 1:
            return False

        # Check clue 17
        if birthday_order[2] != "mar":
            return False

        # Check clue 19
        if pet_order[3] != "dog":
            return False

        # Check clue 1
        if pet_order.index("hamster") <= birthday_order.index("mar"):
            return False

        # Check clue 2
        if birthday_order.index("jan") >= birthday_order.index("sept"):
            return False

        # Check clue 6
        if house_style_order[5] == "mediterranean":
            return False

        return True

    # Initialize solution with a default value
    solution = {
        "solution": "No valid solution found"
    }

    # Find the valid permutation
    for perm in all_permutations:
        if is_valid(perm):
            solution = {
                "solution": {
                    "header": ["House", "Name", "Pet", "HouseStyle", "Birthday"],
                    "rows": [
                        [str(i + 1), names[perm[i]], pets[perm[i]], house_styles[perm[i]], birthdays[perm[i]]]
                        for i in range(6)
                    ]
                }
            }
            break

    return json.dumps(solution, indent=2)

# Output the solution
print(solve_puzzle())