import itertools
import json

def solve_puzzle():
    # Define the attributes
    names = ["Arnold", "Peter", "Bob", "Eric", "Carol", "Alice"]
    animals = ["horse", "rabbit", "fish", "cat", "bird", "dog"]
    occupations = ["engineer", "nurse", "lawyer", "teacher", "artist", "doctor"]
    sports = ["basketball", "volleyball", "soccer", "tennis", "baseball", "swimming"]
    heights = ["average", "tall", "short", "very short", "very tall", "super tall"]

    # Generate all possible permutations
    all_permutations = list(itertools.permutations(range(6)))

    # Check each permutation against the clues
    for name_perm in all_permutations:
        for animal_perm in all_permutations:
            for occupation_perm in all_permutations:
                for sport_perm in all_permutations:
                    for height_perm in all_permutations:
                        # Create dictionaries for quick lookup
                        name_dict = {i+1: names[name_perm[i]] for i in range(6)}
                        animal_dict = {i+1: animals[animal_perm[i]] for i in range(6)}
                        occupation_dict = {i+1: occupations[occupation_perm[i]] for i in range(6)}
                        sport_dict = {i+1: sports[sport_perm[i]] for i in range(6)}
                        height_dict = {i+1: heights[height_perm[i]] for i in range(6)}

                        # Check each clue
                        if (occupation_dict[animal_perm.index(animals.index("dog")) + 1] == "engineer" and
                            height_perm.index(heights.index("average")) < height_perm.index(heights.index("short")) and
                            height_perm.index(heights.index("average")) + 1 == animal_perm.index(animals.index("rabbit")) + 1 and
                            height_perm.index(heights.index("tall")) < height_perm.index(heights.index("very short")) and
                            name_dict[animal_perm.index(animals.index("cat")) + 1] == "Arnold" and
                            occupation_dict[animal_perm.index(animals.index("horse")) + 1] == "teacher" and
                            name_dict[sport_perm.index(sports.index("soccer")) + 1] == "Carol" and
                            height_dict[sport_perm.index(sports.index("volleyball")) + 1] == "tall" and
                            occupation_dict[5] == "lawyer" and
                            sport_dict[occupation_perm.index(occupations.index("teacher")) + 1] == "tennis" and
                            sport_dict[height_perm.index(heights.index("average")) + 1] == "swimming" and
                            sport_perm.index(sports.index("baseball")) + 1 == occupation_perm.index(occupations.index("engineer")) and
                            name_dict[occupation_perm.index(occupations.index("nurse")) + 1] == "Peter" and
                            name_perm.index(names.index("Bob")) > occupation_perm.index(occupations.index("artist")) and
                            occupation_perm.index(occupations.index("teacher")) + 1 == sport_perm.index(sports.index("soccer")) and
                            animal_dict[name_perm.index(names.index("Alice")) + 1] == "rabbit" and
                            animal_dict[name_perm.index(names.index("Carol")) + 1] == "fish" and
                            sport_perm[1] == "baseball" and
                            animal_perm.index(animals.index("cat")) + 1 > height_perm.index(heights.index("very short")) + 1 and
                            height_dict[5] == "super tall"):
                            
                            # Construct the solution
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Animal", "Occupation", "Sport", "Height"],
                                    "rows": [
                                        [str(house), name_dict[house], animal_dict[house], occupation_dict[house], sport_dict[house], height_dict[house]]
                                        for house in range(1, 7)
                                    ]
                                }
                            }
                            return json.dumps(solution, indent=2)

# Run the solver and print the result
print(solve_puzzle())