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
    permutations = list(itertools.permutations(houses))
    solutions = []

    # Iterate over all permutations to find the correct one
    for house_perm in permutations:
        for name_perm in permutations:
            for birthday_perm in permutations:
                for mother_perm in permutations:
                    for occupation_perm in permutations:
                        for hair_color_perm in permutations:
                            # Create a dictionary to store the current permutation
                            current_solution = {
                                "House": house_perm,
                                "Name": name_perm,
                                "Birthday": birthday_perm,
                                "Mother": mother_perm,
                                "Occupation": occupation_perm,
                                "HairColor": hair_color_perm
                            }

                            # Check each clue
                            if (birthday_perm[4] == birthdays.index("mar") and
                                birthday_perm[0] == birthdays.index("feb") and
                                name_perm[occupation_perm.index(occupations.index("doctor"))] == names.index("Eric") and
                                mother_perm[2] == mothers.index("Janelle") and
                                hair_color_perm[occupation_perm.index(occupations.index("artist"))] == hair_colors.index("brown") and
                                house_perm[occupation_perm.index(occupations.index("artist"))] == 4 and
                                mother_perm[hair_color_perm.index(hair_colors.index("black"))] < mother_perm[hair_color_perm.index(hair_colors.index("black"))] and
                                name_perm[hair_color_perm.index(hair_colors.index("black"))] == names.index("Peter") and
                                hair_color_perm[occupation_perm.index(occupations.index("teacher"))] == hair_colors.index("gray") and
                                name_perm[mother_perm.index(mothers.index("Kailyn"))] == names.index("Alice") and
                                house_perm[name_perm.index(names.index("Arnold"))] > house_perm[birthday_perm.index(birthdays.index("sept"))] and
                                hair_color_perm[birthday_perm.index(birthdays.index("jan"))] == hair_colors.index("brown") and
                                name_perm[hair_color_perm.index(hair_colors.index("blonde"))] == names.index("Arnold") and
                                mother_perm[hair_color_perm.index(hair_colors.index("black"))] == mothers.index("Holly") and
                                name_perm[occupation_perm.index(occupations.index("lawyer"))] == names.index("Peter") and
                                birthday_perm[mother_perm.index(mothers.index("Kailyn"))] > birthday_perm[birthdays.index("sept")] and
                                hair_color_perm[name_perm.index(names.index("Alice"))] == hair_colors.index("gray")):
                                
                                # If all clues are satisfied, add the solution
                                solutions.append(current_solution)

    # Format the solution as required
    formatted_solution = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Mother", "Occupation", "HairColor"],
            "rows": []
        }
    }

    # Assuming there's only one valid solution
    if solutions:
        solution = solutions[0]
        for i in range(5):
            formatted_solution["solution"]["rows"].append([
                str(solution["House"][i] + 1),
                names[solution["Name"][i]],
                birthdays[solution["Birthday"][i]],
                mothers[solution["Mother"][i]],
                occupations[solution["Occupation"][i]],
                hair_colors[solution["HairColor"][i]]
            ])

    return json.dumps(formatted_solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())