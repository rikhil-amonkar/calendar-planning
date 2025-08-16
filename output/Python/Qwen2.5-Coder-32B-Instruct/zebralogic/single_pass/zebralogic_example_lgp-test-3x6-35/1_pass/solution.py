import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Eric", "Arnold", "Peter"]
    vacations = ["mountain", "city", "beach"]
    heights = ["very short", "average", "short"]
    flowers = ["carnations", "daffodils", "lilies"]
    hair_colors = ["brown", "black", "blonde"]
    educations = ["associate", "bachelor", "high school"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(vacations)) * \
                       list(itertools.permutations(heights)) * \
                       list(itertools.permutations(flowers)) * \
                       list(itertools.permutations(hair_colors)) * \
                       list(itertools.permutations(educations))

    # Check each permutation against the clues
    for names_perm, vacations_perm, heights_perm, flowers_perm, hair_colors_perm, educations_perm in zip(
            itertools.permutations(names),
            itertools.permutations(vacations),
            itertools.permutations(heights),
            itertools.permutations(flowers),
            itertools.permutations(hair_colors),
            itertools.permutations(educations)
    ):
        # Unpack the permutations for easier reference
        name1, name2, name3 = names_perm
        vacation1, vacation2, vacation3 = vacations_perm
        height1, height2, height3 = heights_perm
        flower1, flower2, flower3 = flowers_perm
        hair_color1, hair_color2, hair_color3 = hair_colors_perm
        education1, education2, education3 = educations_perm

        # Apply the clues
        if (name3 == "Peter" and height2 == "average" and
            flower2 == "daffodils" and name2 == "Arnold" and
            height2 != "very short" and vacation1 == "beach" and
            education3 == "high school" and height3 > height1 and
            flower3 == "lilies" and name3 == "Eric" and
            education3 == "bachelor" and vacation2 == "city" and
            hair_color3 == "blonde" and vacation1 == "beach" and
            hair_color1 == "brown"):
            # Construct the solution in the required format
            solution = {
                "solution": {
                    "header": ["House", "Name", "Vacation", "Height", "Flower", "HairColor", "Education"],
                    "rows": [
                        ["1", name1, vacation1, height1, flower1, hair_color1, education1],
                        ["2", name2, vacation2, height2, flower2, hair_color2, education2],
                        ["3", name3, vacation3, height3, flower3, hair_color3, education3]
                    ]
                }
            }
            return json.dumps(solution, indent=2)

# Print the solution
print(solve_puzzle())