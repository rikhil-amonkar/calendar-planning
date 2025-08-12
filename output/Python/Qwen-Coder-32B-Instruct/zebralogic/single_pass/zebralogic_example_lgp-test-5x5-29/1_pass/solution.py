import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]
    names = ["Eric", "Peter", "Alice", "Bob", "Arnold"]
    nationalities = ["norwegian", "brit", "swede", "dane", "german"]
    vacations = ["cruise", "mountain", "camping", "beach", "city"]
    educations = ["bachelor", "master", "associate", "doctorate", "high school"]
    occupations = ["artist", "doctor", "engineer", "teacher", "lawyer"]

    # Generate all possible permutations
    all_permutations = list(itertools.permutations(range(5)))

    for name_perm in all_permutations:
        for nationality_perm in all_permutations:
            for vacation_perm in all_permutations:
                for education_perm in all_permutations:
                    for occupation_perm in all_permutations:
                        # Create a mapping from index to attribute
                        name_map = {i: names[name_perm[i]] for i in range(5)}
                        nationality_map = {i: nationalities[nationality_perm[i]] for i in range(5)}
                        vacation_map = {i: vacations[vacation_perm[i]] for i in range(5)}
                        education_map = {i: educations[education_perm[i]] for i in range(5)}
                        occupation_map = {i: occupations[occupation_perm[i]] for i in range(5)}

                        # Check all constraints
                        if (vacation_map[vacation_perm.index("cruise")] == occupation_map[occupation_perm.index("lawyer")] and
                            vacation_map[vacation_perm.index("beach")] + 1 == name_perm.index("Arnold") and
                            education_map[education_perm.index("doctorate")] < name_perm.index("Bob") and
                            education_map[education_perm.index("associate")] == vacation_map[vacation_perm.index("cruise")] and
                            name_perm.index("Peter") != 0 and
                            occupation_map[occupation_perm.index("artist")] == "Peter" and
                            education_map[education_perm.index("master")] == vacation_map[vacation_perm.index("camping")] and
                            nationality_map[nationality_perm.index("dane")] > occupation_perm.index("doctor") and
                            education_map[education_perm.index("associate")] + 1 == occupation_perm.index("engineer") and
                            nationality_map[nationality_perm.index("brit")] == vacation_map[vacation_perm.index("camping")] and
                            abs(nationality_perm.index("norwegian") - education_perm.index("bachelor")) == 1 and
                            occupation_map[occupation_perm.index("artist")] == "swede" and
                            name_perm.index("Bob") != 3 and
                            name_map[vacation_perm.index("camping")] == "Eric" and
                            name_map[name_perm.index("Alice")] == "German" and
                            vacation_map[vacation_perm.index("beach")] < vacation_perm.index("city") and
                            vacation_map[vacation_perm.index("mountain")] == "house 5" and
                            vacation_map[vacation_perm.index("cruise")] > vacation_map[vacation_perm.index("beach")] and
                            education_map[education_perm.index("bachelor")] == 2):
                            
                            # Construct the solution
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Nationality", "Vacation", "Education", "Occupation"],
                                    "rows": []
                                }
                            }
                            for house in houses:
                                solution["solution"]["rows"].append([
                                    str(house),
                                    name_map[house-1],
                                    nationality_map[house-1],
                                    vacation_map[house-1],
                                    education_map[house-1],
                                    occupation_map[house-1]
                                ])
                            
                            return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())