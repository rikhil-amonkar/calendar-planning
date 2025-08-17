import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    houses = [1, 2, 3, 4, 5]
    names = ["Alice", "Eric", "Bob", "Peter", "Arnold"]
    birthdays = ["mar", "april", "sept", "feb", "jan"]
    mothers = ["Holly", "Janelle", "Kailyn", "Penny", "Aniya"]
    occupations = ["engineer", "doctor", "lawyer", "artist", "teacher"]
    hair_colors = ["red", "blonde", "black", "gray", "brown"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(names)) + \
                       list(itertools.permutations(birthdays)) + \
                       list(itertools.permutations(mothers)) + \
                       list(itertools.permutations(occupations)) + \
                       list(itertools.permutations(hair_colors))

    # Check each combination of permutations
    for names_perm in all_permutations[:len(names)]:
        for birthdays_perm in all_permutations[len(names):2*len(names)]:
            for mothers_perm in all_permutations[2*len(names):3*len(names)]:
                for occupations_perm in all_permutations[3*len(names):4*len(names)]:
                    for hair_colors_perm in all_permutations[4*len(names):]:
                        # Create a dictionary to store the current permutation
                        current_solution = {house: {} for house in houses}
                        for i in range(len(houses)):
                            current_solution[houses[i]]["Name"] = names_perm[i]
                            current_solution[houses[i]]["Birthday"] = birthdays_perm[i]
                            current_solution[houses[i]]["Mother"] = mothers_perm[i]
                            current_solution[houses[i]]["Occupation"] = occupations_perm[i]
                            current_solution[houses[i]]["HairColor"] = hair_colors_perm[i]

                        # Check all the clues
                        if (current_solution[5]["Birthday"] == "mar" and
                            current_solution[1]["Birthday"] == "feb" and
                            current_solution[names_perm.index("Eric")]["Occupation"] == "doctor" and
                            current_solution[3]["Mother"] == "Janelle" and
                            current_solution[hair_colors_perm.index("brown")]["Occupation"] == "artist" and
                            current_solution[4]["Occupation"] == "artist" and
                            mothers_perm.index("Penny") < hair_colors_perm.index("black") and
                            current_solution[names_perm.index("Peter")]["HairColor"] == "black" and
                            current_solution[hair_colors_perm.index("gray")]["Occupation"] == "teacher" and
                            current_solution[names_perm.index("Alice")]["Mother"] == "Kailyn" and
                            names_perm.index("Arnold") > birthdays_perm.index("sept") and
                            current_solution[hair_colors_perm.index("brown")]["Birthday"] == "jan" and
                            current_solution[names_perm.index("Arnold")]["HairColor"] == "blonde" and
                            current_solution[mothers_perm.index("Holly")]["HairColor"] == "black" and
                            current_solution[names_perm.index("Peter")]["Occupation"] == "lawyer" and
                            birthdays_perm.index("sept") < mothers_perm.index("Kailyn") and
                            current_solution[names_perm.index("Alice")]["HairColor"] == "gray"):
                            # If all clues are satisfied, format the solution
                            solution_rows = []
                            for house in houses:
                                row = [str(house)]
                                for key in ["Name", "Birthday", "Mother", "Occupation", "HairColor"]:
                                    row.append(current_solution[house][key])
                                solution_rows.append(row)
                            solution_dict = {
                                "solution": {
                                    "header": ["House", "Name", "Birthday", "Mother", "Occupation", "HairColor"],
                                    "rows": solution_rows
                                }
                            }
                            return json.dumps(solution_dict, indent=2)

# Run the solver and print the result
print(solve_puzzle())