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
                        try:
                            jan_house = birthday_perm.index("jan") + 1
                            bachelor_house = education_perm.index("bachelor") + 1
                            arnold_house = name_perm.index("Arnold") + 1
                            painting_house = hobby_perm.index("painting") + 1
                            sept_house = birthday_perm.index("sept") + 1
                            april_house = birthday_perm.index("april") + 1
                            feb_house = birthday_perm.index("feb") + 1

                            if (current_solution[f"house{jan_house}"]["smoothie"] == "desert" and
                                current_solution[f"house{bachelor_house}"]["birthday"] == "jan" and
                                current_solution[f"house{bachelor_house}"]["name"] == "Eric" and
                                current_solution["house3"]["education"] == "high school" and
                                current_solution["house3"]["smoothie"] != "watermelon" and
                                current_solution[f"house{arnold_house}"]["education"] == "associate" and
                                current_solution[f"house{painting_house}"]["education"] == "master" and
                                abs(sept_house - birthday_perm.index("april") - 1) == 2 and
                                current_solution[f"house{sept_house}"]["education"] == "high school" and
                                current_solution[f"house{name_perm.index('Alice') + 1}"]["hobby"] == "cooking" and
                                abs(april_house - hobby_perm.index("gardening") - 1) == 1 and
                                current_solution[f"house{feb_house}"]["hobby"] == "painting"):
                                
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
                        except ValueError:
                            # Skip this permutation if any index operation fails
                            continue

# Run the function and print the result
print(solve_puzzle())