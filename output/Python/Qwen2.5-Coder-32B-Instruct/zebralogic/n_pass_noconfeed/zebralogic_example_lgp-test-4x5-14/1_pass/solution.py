import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Peter", "Alice", "Eric", "Arnold"]
    mothers = ["Janelle", "Holly", "Aniya", "Kailyn"]
    smoothies = ["watermelon", "dragonfruit", "desert", "cherry"]
    heights = ["tall", "average", "short", "very short"]
    educations = ["high school", "associate", "master", "bachelor"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(range(4)))

    # Iterate over all possible combinations of permutations
    for name_perm in all_permutations:
        for mother_perm in all_permutations:
            for smoothie_perm in all_permutations:
                for height_perm in all_permutations:
                    for education_perm in all_permutations:
                        # Create a dictionary to store the current assignment
                        assignment = {
                            "name": {i+1: names[name_perm[i]] for i in range(4)},
                            "mother": {i+1: mothers[mother_perm[i]] for i in range(4)},
                            "smoothie": {i+1: smoothies[smoothie_perm[i]] for i in range(4)},
                            "height": {i+1: heights[height_perm[i]] for i in range(4)},
                            "education": {i+1: educations[education_perm[i]] for i in range(4)}
                        }

                        # Check all the clues
                        if (assignment["mother"][3] == "Janelle" and
                            assignment["smoothie"][smoothie_perm.index(smoothies.index("desert")) + 1] == "desert" and
                            assignment["education"][smoothie_perm.index(smoothies.index("desert")) + 1] == "master" and
                            smoothie_perm.index(smoothies.index("desert")) != 0 and
                            height_perm.index(heights.index("very short")) < education_perm.index(educations.index("high school")) and
                            abs(name_perm.index(names.index("Eric")) - smoothie_perm.index(smoothies.index("cherry"))) == 1 and
                            education_perm.index(educations.index("high school")) != 2 and
                            assignment["mother"][mother_perm.index(mothers.index("Kailyn")) + 1] == "Kailyn" and
                            assignment["education"][mother_perm.index(mothers.index("Kailyn")) + 1] == "associate" and
                            assignment["mother"][smoothie_perm.index(smoothies.index("cherry")) + 1] == "Aniya" and
                            assignment["height"][mother_perm.index(mothers.index("Janelle")) + 1] == "tall" and
                            name_perm.index(names.index("Alice")) > height_perm.index(heights.index("average")) and
                            smoothie_perm.index(smoothies.index("dragonfruit")) + 1 == height_perm.index(heights.index("short")) and
                            assignment["height"][name_perm.index(names.index("Alice")) + 1] == "tall"):
                            
                            # If all clues are satisfied, format the solution
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Mother", "Smoothie", "Height", "Education"],
                                    "rows": [
                                        [str(house), assignment["name"][house], assignment["mother"][house], assignment["smoothie"][house], assignment["height"][house], assignment["education"][house]]
                                        for house in range(1, 5)
                                    ]
                                }
                            }
                            return json.dumps(solution, indent=4)

# Solve the puzzle and print the result
print(solve_puzzle())