import itertools
import json

def solve_puzzle():
    # Define the attributes
    names = ["Peter", "Bob", "Carol", "Eric", "Alice", "Arnold"]
    pets = ["bird", "dog", "cat", "rabbit", "fish", "hamster"]
    house_styles = ["victorian", "ranch", "modern", "mediterranean", "colonial", "craftsman"]
    birth_months = ["mar", "sept", "may", "feb", "jan", "april"]

    # Generate all possible permutations
    all_permutations = list(itertools.permutations(range(6)))

    # Function to check if a permutation satisfies all clues
    def is_valid(permutation):
        # Unpack the permutation into separate lists
        name_order = [names[i] for i in permutation]
        pet_order = [pets[i] for i in permutation]
        house_style_order = [house_styles[i] for i in permutation]
        birth_month_order = [birth_months[i] for i in permutation]

        # Check each clue
        if pet_order.index("hamster") <= birth_month_order.index("mar"):
            return False
        if birth_month_order.index("jan") >= birth_month_order.index("sept"):
            return False
        if birth_month_order[1] != "may":
            return False
        if house_style_order[1] != "colonial":
            return False
        if name_order[2] != "Carol":
            return False
        if house_style_order[5] == "mediterranean":
            return False
        if name_order.index("Bob") >= pet_order.index("fish"):
            return False
        if name_order[5] != "Eric":
            return False
        if abs(pet_order.index("cat") - house_style_order.index("victorian")) != 1:
            return False
        if abs(house_style_order.index("victorian") - pet_order.index("hamster")) != 2:
            return False
        if name_order[house_style_order.index("craftsman")] != "Arnold":
            return False
        if house_style_order.index("colonial") >= house_style_order.index("modern"):
            return False
        if pet_order[1] == "fish":
            return False
        if name_order[house_style_order.index("colonial")] != "Peter":
            return False
        if birth_month_order.index("jan") + 1 != birth_month_order.index("april"):
            return False
        if abs(pet_order.index("bird") - house_style_order.index("modern")) != 1:
            return False
        if name_order[birth_month_order.index("mar")] != "Carol":
            return False
        if house_style_order[3] != "craftsman":
            return False
        if pet_order[3] != "dog":
            return False

        return True

    # Find the valid permutation
    for permutation in all_permutations:
        if is_valid(permutation):
            # Unpack the permutation into separate lists
            name_order = [names[i] for i in permutation]
            pet_order = [pets[i] for i in permutation]
            house_style_order = [house_styles[i] for i in permutation]
            birth_month_order = [birth_months[i] for i in permutation]

            # Prepare the solution in JSON format
            solution = {
                "solution": {
                    "header": ["House", "Name", "Pet", "House Style", "Birth Month"],
                    "rows": []
                }
            }

            for i in range(6):
                solution["solution"]["rows"].append([
                    str(i + 1),
                    name_order[i],
                    pet_order[i],
                    house_style_order[i],
                    birth_month_order[i]
                ])

            return json.dumps(solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())