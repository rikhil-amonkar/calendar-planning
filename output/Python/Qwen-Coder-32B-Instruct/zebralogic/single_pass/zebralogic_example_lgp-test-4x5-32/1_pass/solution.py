import itertools
import json

def solve_puzzle():
    # Define the attributes and their possible values
    names = ["Arnold", "Alice", "Eric", "Peter"]
    hobbies = ["cooking", "painting", "photography", "gardening"]
    birthdays = ["april", "jan", "sept", "feb"]
    educations = ["master", "bachelor", "associate", "high school"]
    smoothies = ["cherry", "watermelon", "desert", "dragonfruit"]

    # Generate all possible permutations for each attribute
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(hobbies)) * \
                       list(itertools.permutations(birthdays)) * \
                       list(itertools.permutations(educations)) * \
                       list(itertools.permutations(smoothies))

    # Function to check if a permutation satisfies all the clues
    def is_valid_solution(solution):
        name, hobby, birthday, education, smoothie = solution

        # Unpack the tuples for easier access
        name1, name2, name3, name4 = name
        hobby1, hobby2, hobby3, hobby4 = hobby
        birthday1, birthday2, birthday3, birthday4 = birthday
        education1, education2, education3, education4 = education
        smoothie1, smoothie2, smoothie3, smoothie4 = smoothie

        # Check each clue
        if smoothie[birthday.index("jan")] != "desert":
            return False
        if name[education.index("bachelor")] != "Eric":
            return False
        if name[birthday.index("jan")] != name[education.index("bachelor")]:
            return False
        if education3 != "high school":
            return False
        if smoothie3 == "watermelon":
            return False
        if name[education.index("associate")] != "Arnold":
            return False
        if name[education.index("master")] != name[hobby.index("painting")]:
            return False
        if abs(birthday.index("dragonfruit") - birthday.index("sept")) != 2:
            return False
        if name[education.index("high school")] != name[birthday.index("sept")]:
            return False
        if name[hobby.index("cooking")] != "Alice":
            return False
        if abs(birthday.index("april") - birthday.index("gardening")) != 1:
            return False
        if name[hobby.index("painting")] != name[birthday.index("feb")]:
            return False

        return True

    # Iterate through all permutations to find a valid solution
    for perm in itertools.product(all_permutations, repeat=1):
        solution = list(zip(*perm))[0]
        if is_valid_solution(solution):
            break

    # Prepare the result in the required format
    result = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Birthday", "Education", "Smoothie"],
            "rows": [
                ["1", solution[0][0], solution[1][0], solution[2][0], solution[3][0], solution[4][0]],
                ["2", solution[0][1], solution[1][1], solution[2][1], solution[3][1], solution[4][1]],
                ["3", solution[0][2], solution[1][2], solution[2][2], solution[3][2], solution[4][2]],
                ["4", solution[0][3], solution[1][3], solution[2][3], solution[3][3], solution[4][3]]
            ]
        }
    }

    # Output the result as JSON
    print(json.dumps(result, indent=2))

# Run the solver
solve_puzzle()