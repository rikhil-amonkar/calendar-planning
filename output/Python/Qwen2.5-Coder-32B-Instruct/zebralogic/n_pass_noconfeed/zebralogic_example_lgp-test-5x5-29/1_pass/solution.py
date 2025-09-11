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
    all_permutations = list(itertools.permutations(names))
    for name_perm in all_permutations:
        if name_perm[1] != "Peter" or name_perm[3] == "Bob" or name_perm[2] != "Eric" or name_perm[4] != "Arnold":
            continue

        for nationality_perm in all_permutations:
            if nationality_perm[2] != "swede" or nationality_perm[1] != "brit" or nationality_perm[4] != "german":
                continue

            for vacation_perm in all_permutations:
                if vacation_perm[1] != "beach" or vacation_perm[2] != "camping" or vacation_perm[4] != "mountain" or vacation_perm[3] != "city":
                    continue

                for education_perm in all_permutations:
                    if education_perm[2] != "bachelor" or education_perm[1] != "master" or education_perm[3] != "associate":
                        continue

                    for occupation_perm in all_permutations:
                        if occupation_perm[1] != "artist" or occupation_perm[4] != "doctor" or occupation_perm[3] != "engineer" or occupation_perm[2] != "lawyer":
                            continue

                        # Check constraints
                        if (vacation_perm.index("cruise") != occupation_perm.index("lawyer") or
                            vacation_perm.index("beach") + 1 != name_perm.index("Arnold") or
                            education_perm.index("doctorate") > name_perm.index("Bob") or
                            education_perm.index("associate") != vacation_perm.index("cruise") or
                            education_perm.index("associate") + 1 != occupation_perm.index("engineer") or
                            nationalities.index("danish") < occupation_perm.index("doctor") or
                            abs(nationalities.index("norwegian") - education_perm.index("bachelor")) != 1 or
                            vacation_perm.index("beach") >= vacation_perm.index("city") or
                            vacation_perm.index("beach") >= vacation_perm.index("cruise")):
                            continue

                        # If all constraints are satisfied, construct the solution
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Nationality", "Vacation", "Education", "Occupation"],
                                "rows": []
                            }
                        }
                        for i in range(5):
                            solution["solution"]["rows"].append([
                                str(houses[i]),
                                name_perm[i],
                                nationality_perm[i],
                                vacation_perm[i],
                                education_perm[i],
                                occupation_perm[i]
                            ])
                        return json.dumps(solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())