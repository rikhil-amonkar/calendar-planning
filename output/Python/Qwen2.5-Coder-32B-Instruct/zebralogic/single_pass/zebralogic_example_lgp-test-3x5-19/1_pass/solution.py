import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Arnold", "Peter", "Eric"]
    occupations = ["doctor", "teacher", "engineer"]
    educations = ["associate", "high school", "bachelor"]
    smoothies = ["desert", "cherry", "watermelon"]
    hobbies = ["gardening", "cooking", "photography"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(names)) + \
                       list(itertools.permutations(occupations)) + \
                       list(itertools.permutations(educations)) + \
                       list(itertools.permutations(smoothies)) + \
                       list(itertools.permutations(hobbies))

    # Iterate over all possible combinations of permutations
    for names_perm, occupations_perm, educations_perm, smoothies_perm, hobbies_perm in itertools.product(all_permutations, repeat=5):
        # Unpack the permutations into individual lists for each category
        name1, name2, name3 = names_perm
        occupation1, occupation2, occupation3 = occupations_perm
        education1, education2, education3 = educations_perm
        smoothie1, smoothie2, smoothie3 = smoothies_perm
        hobby1, hobby2, hobby3 = hobbies_perm

        # Apply the clues to filter out invalid combinations
        if (smoothie1 == "desert" and occupation1 != "doctor") or \
           (smoothie2 == "desert" and occupation2 != "doctor") or \
           (smoothie3 == "desert" and occupation3 != "doctor"):
            continue

        if name3 == "Arnold":
            continue

        if (name1 == "Peter" and smoothie2 != "cherry") and \
           (name1 == "Peter" and smoothie3 != "cherry") and \
           (name2 == "Peter" and smoothie3 != "cherry"):
            continue

        if (hobby2 != "cooking"):
            continue

        if (name2 != "Peter"):
            continue

        if (hobby1 == "gardening" and education2 != "associate") and \
           (hobby1 == "gardening" and education3 != "associate") and \
           (hobby2 == "gardening" and education3 != "associate"):
            continue

        if (smoothie1 == "desert" and education2 != "bachelor") and \
           (smoothie1 == "desert" and education3 != "bachelor") and \
           (smoothie2 == "desert" and education3 != "bachelor"):
            continue

        if (occupation2 != "doctor"):
            continue

        if (occupation3 != "teacher"):
            continue

        # If all clues are satisfied, construct the solution
        solution = {
            "solution": {
                "header": ["House", "Name", "Occupation", "Education", "Smoothie", "Hobby"],
                "rows": [
                    ["1", name1, occupation1, education1, smoothie1, hobby1],
                    ["2", name2, occupation2, education2, smoothie2, hobby2],
                    ["3", name3, occupation3, education3, smoothie3, hobby3]
                ]
            }
        }

        # Output the solution as JSON
        print(json.dumps(solution, indent=2))
        return

# Run the function to solve the puzzle
solve_puzzle()