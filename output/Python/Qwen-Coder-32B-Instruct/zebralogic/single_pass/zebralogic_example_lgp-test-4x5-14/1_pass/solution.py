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

    # Iterate over all possible combinations
    for name_order in all_permutations:
        for mother_order in all_permutations:
            for smoothie_order in all_permutations:
                for height_order in all_permutations:
                    for education_order in all_permutations:
                        # Create dictionaries to map orders to actual values
                        name_map = {i: names[name_order[i]] for i in range(4)}
                        mother_map = {i: mothers[mother_order[i]] for i in range(4)}
                        smoothie_map = {i: smoothies[smoothie_order[i]] for i in range(4)}
                        height_map = {i: heights[height_order[i]] for i in range(4)}
                        education_map = {i: educations[education_order[i]] for i in range(4)}

                        # Check all the clues
                        if (mother_map[2] == "Janelle" and
                            smoothie_map[desert_house := smoothie_order.index(smoothies.index("desert"))] == "desert" and
                            desert_house != 0 and
                            height_order.index(heights.index("very short")) < education_order.index(educations.index("high school")) and
                            abs(name_order[names.index("Eric")] - smoothie_order[smoothies.index("cherry")]) == 1 and
                            education_order.index(educations.index("high school")) != 2 and
                            mother_map[associate_house := education_order.index(educations.index("associate"))] == "Kailyn" and
                            mother_map[cherry_house := smoothie_order.index(smoothies.index("cherry"))] == "Aniya" and
                            height_map[janelle_house := mother_order.index(mothers.index("Janelle"))] == "tall" and
                            name_order[names.index("Arnold")] > height_order.index(heights.index("average")) and
                            smoothie_order.index(smoothies.index("dragonfruit")) + 1 == height_order.index(heights.index("short")) and
                            name_map[tall_house := height_order.index(heights.index("tall"))] == "Alice"):
                            
                            # Construct the solution
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Mother", "Smoothie", "Height", "Education"],
                                    "rows": [
                                        [str(i+1), name_map[i], mother_map[i], smoothie_map[i], height_map[i], education_map[i]]
                                        for i in range(4)
                                    ]
                                }
                            }
                            return json.dumps(solution, indent=2)

# Run the solver and print the result
print(solve_puzzle())