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
    all_permutations = list(itertools.permutations(houses))

    for name_perm in all_permutations:
        for nationality_perm in all_permutations:
            for vacation_perm in all_permutations:
                for education_perm in all_permutations:
                    for occupation_perm in all_permutations:
                        # Create a dictionary to map each attribute to its position
                        name_map = dict(zip(houses, name_perm))
                        nationality_map = dict(zip(houses, nationality_perm))
                        vacation_map = dict(zip(houses, vacation_perm))
                        education_map = dict(zip(houses, education_perm))
                        occupation_map = dict(zip(houses, occupation_perm))

                        # Check all clues
                        if (vacation_map[name_perm.index("Eric")] == "camping" and
                            vacation_map[name_perm.index("Arnold") - 1] == "beach" and
                            education_map[name_perm.index("Arnold") - 1] == "associate" and
                            education_map[name_perm.index("Arnold") - 2] == "doctorate" and
                            name_perm[0] != "Peter" and
                            name_perm[occupation_perm.index("artist")] == "Peter" and
                            education_map[vacation_perm.index("camping")] == "master" and
                            nationality_map[occupation_perm.index("doctor")] < nationality_map[occupation_perm.index("artist")] and
                            education_map[occupation_perm.index("associate")] + 1 == occupation_perm.index("engineer") and
                            nationality_map[vacation_perm.index("camping")] == "brit" and
                            abs(nationality_perm.index("norwegian") - education_perm.index("bachelor")) == 1 and
                            nationality_map[occupation_perm.index("artist")] == "swede" and
                            name_perm[3] != "Bob" and
                            education_map[vacation_perm.index("camping")] == "master" and
                            name_perm[nationality_perm.index("german")] == "Alice" and
                            vacation_map[vacation_perm.index("beach")] < vacation_map[vacation_perm.index("city")] and
                            vacation_map[name_perm.index("Bob")] == "mountain" and
                            vacation_map[occupation_perm.index("lawyer")] == "cruise" and
                            education_map[vacation_perm.index("beach")] + 1 == occupation_perm.index("lawyer") and
                            education_map[2] == "bachelor"):
                            
                            # If all conditions are satisfied, construct the solution
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Nationality", "Vacation", "Education", "Occupation"],
                                    "rows": []
                                }
                            }
                            
                            for house in houses:
                                solution["solution"]["rows"].append([
                                    str(house),
                                    name_map[house],
                                    nationality_map[house],
                                    vacation_map[house],
                                    education_map[house],
                                    occupation_map[house]
                                ])
                            
                            return json.dumps(solution, indent=2)

# Run the solver and print the result
print(solve_puzzle())