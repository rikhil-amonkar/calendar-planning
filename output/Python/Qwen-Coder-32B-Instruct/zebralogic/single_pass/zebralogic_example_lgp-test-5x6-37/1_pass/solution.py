import itertools
import json

# Define the possible values for each attribute
names = ["Bob", "Arnold", "Alice", "Peter", "Eric"]
hobbies = ["cooking", "gardening", "painting", "photography", "knitting"]
sports = ["swimming", "tennis", "soccer", "baseball", "basketball"]
house_styles = ["ranch", "craftsman", "victorian", "modern", "colonial"]
children = ["Timothy", "Samantha", "Bella", "Meredith", "Fred"]
heights = ["average", "very tall", "very short", "short", "tall"]

# Generate all possible permutations for the attributes
permutations = list(itertools.permutations(range(5)))

# Function to check if a given permutation satisfies all the clues
def is_valid_solution(house_names, house_hobbies, house_sports, house_styles, house_children, house_heights):
    # Clue 1
    if house_children[house_heights.index(heights.index("average"))] != children.index("Meredith"):
        return False
    # Clue 2
    if house_heights[1] != heights.index("tall"):
        return False
    # Clue 3
    if house_styles[house_names.index(names.index("Peter")) + 1] != house_styles.index("victorian"):
        return False
    # Clue 4
    if house_heights[house_names.index(names.index("Alice"))] != heights.index("tall"):
        return False
    # Clue 5
    if house_sports[house_heights.index(heights.index("very tall"))] != sports.index("baseball"):
        return False
    # Clue 6
    if abs(house_children.index(children.index("Meredith")) - house_children.index(children.index("Timothy"))) != 1:
        return False
    # Clue 7
    if house_hobbies[house_names.index(names.index("Bob"))] != hobbies.index("painting"):
        return False
    # Clue 8
    if house_hobbies[1] != hobbies.index("gardening"):
        return False
    # Clue 9
    if house_names.index(names.index("Eric")) < house_heights.index(heights.index("very short")):
        return False
    # Clue 10
    if house_children[house_sports.index(sports.index("tennis"))] != children.index("Samantha"):
        return False
    # Clue 11
    if house_sports[0] == sports.index("soccer"):
        return False
    # Clue 12
    if house_styles[house_children.index(children.index("Samantha"))] != house_styles.index("modern"):
        return False
    # Clue 13
    if house_heights[house_styles.index("craftsman")] != heights.index("average"):
        return False
    # Clue 14
    if house_children[house_styles.index("victorian")] != children.index("Fred"):
        return False
    # Clue 15
    if house_sports[house_heights.index(heights.index("short"))] != sports.index("basketball"):
        return False
    # Clue 16
    if house_heights[house_names.index(names.index("Peter"))] != heights.index("very tall"):
        return False
    # Clue 17
    if house_styles.index("ranch") > house_hobbies.index(hobbies.index("cooking")):
        return False
    # Clue 18
    if abs(house_hobbies.index(hobbies.index("knitting")) - house_hobbies.index(hobbies.index("gardening"))) != 1:
        return False
    # Clue 19
    if house_hobbies[house_styles.index("modern")] != hobbies.index("cooking"):
        return False
    # Clue 20
    if house_styles[4] != house_styles.index("victorian"):
        return False
    return True

# Iterate over all permutations to find the valid solution
for perm in permutations:
    house_names = perm
    for perm in permutations:
        house_hobbies = perm
        for perm in permutations:
            house_sports = perm
            for perm in permutations:
                house_styles = perm
                for perm in permutations:
                    house_children = perm
                    for perm in permutations:
                        house_heights = perm
                        if is_valid_solution(house_names, house_hobbies, house_sports, house_styles, house_children, house_heights):
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Hobby", "Sport", "House Style", "Child", "Height"],
                                    "rows": []
                                }
                            }
                            for i in range(5):
                                solution["solution"]["rows"].append([
                                    str(i + 1),
                                    names[house_names[i]],
                                    hobbies[house_hobbies[i]],
                                    sports[house_sports[i]],
                                    house_styles[house_styles[i]],
                                    children[house_children[i]],
                                    heights[house_heights[i]]
                                ])
                            print(json.dumps(solution, indent=2))
                            exit()