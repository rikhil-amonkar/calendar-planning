import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Arnold", "Alice", "Eric", "Peter"]
    hobbies = ["cooking", "painting", "photography", "gardening"]
    birthdays = ["april", "jan", "sept", "feb"]
    educations = ["master", "bachelor", "associate", "high school"]
    smoothies = ["cherry", "watermelon", "desert", "dragonfruit"]

    # Generate all possible permutations
    permutations = list(itertools.permutations(range(4)))

    # Check each permutation against the clues
    for name_perm in permutations:
        for hobby_perm in permutations:
            for birthday_perm in permutations:
                for education_perm in permutations:
                    for smoothie_perm in permutations:
                        # Create a dictionary to store the current permutation
                        current_solution = {
                            "house1": {"name": names[name_perm[0]], "hobby": hobbies[hobby_perm[0]],
                                       "birthday": birthdays[birthday_perm[0]], "education": educations[education_perm[0]],
                                       "smoothie": smoothies[smoothie_perm[0]]},
                            "house2": {"name": names[name_perm[1]], "hobby": hobbies[hobby_perm[1]],
                                       "birthday": birthdays[birthday_perm[1]], "education": educations[education_perm[1]],
                                       "smoothie": smoothies[smoothie_perm[1]]},
                            "house3": {"name": names[name_perm[2]], "hobby": hobbies[hobby_perm[2]],
                                       "birthday": birthdays[birthday_perm[2]], "education": educations[education_perm[2]],
                                       "smoothie": smoothies[smoothie_perm[2]]},
                            "house4": {"name": names[name_perm[3]], "hobby": hobbies[hobby_perm[3]],
                                       "birthday": birthdays[birthday_perm[3]], "education": educations[education_perm[3]],
                                       "smoothie": smoothies[smoothie_perm[3]]}
                        }

                        # Apply the clues
                        if (current_solution["house" + str(birthday_perm.index("jan") + 1)]["smoothie"] == "desert" and
                            current_solution["house" + str(education_perm.index("bachelor") + 1)]["birthday"] == "jan" and
                            current_solution["house" + str(education_perm.index("bachelor") + 1)]["name"] == "Eric" and
                            current_solution["house3"]["education"] == "high school" and
                            current_solution["house3"]["smoothie"] != "watermelon" and
                            current_solution["house" + str(name_perm.index("Arnold") + 1)]["education"] == "associate" and
                            current_solution["house" + str(hobby_perm.index("painting") + 1)]["education"] == "master" and
                            abs(birthday_perm.index("sept") - birthday_perm.index("dragonfruit")) == 2 and
                            current_solution["house" + str(birthday_perm.index("sept") + 1)]["education"] == "high school" and
                            current_solution["house" + str(name_perm.index("Alice") + 1)]["hobby"] == "cooking" and
                            abs(birthday_perm.index("april") - birthday_perm.index("gardening")) == 1 and
                            current_solution["house" + str(birthday_perm.index("feb") + 1)]["hobby"] == "painting"):
                            
                            # Format the solution as required
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Hobby", "Birthday", "Education", "Smoothie"],
                                    "rows": [
                                        ["1", current_solution["house1"]["name"], current_solution["house1"]["hobby"],
                                         current_solution["house1"]["birthday"], current_solution["house1"]["education"],
                                         current_solution["house1"]["smoothie"]],
                                        ["2", current_solution["house2"]["name"], current_solution["house2"]["hobby"],
                                         current_solution["house2"]["birthday"], current_solution["house2"]["education"],
                                         current_solution["house2"]["smoothie"]],
                                        ["3", current_solution["house3"]["name"], current_solution["house3"]["hobby"],
                                         current_solution["house3"]["birthday"], current_solution["house3"]["education"],
                                         current_solution["house3"]["smoothie"]],
                                        ["4", current_solution["house4"]["name"], current_solution["house4"]["hobby"],
                                         current_solution["house4"]["birthday"], current_solution["house4"]["education"],
                                         current_solution["house4"]["smoothie"]]
                                    ]
                                }
                            }
                            return json.dumps(solution, indent=2)

# Run the function and print the result
print(solve_puzzle())