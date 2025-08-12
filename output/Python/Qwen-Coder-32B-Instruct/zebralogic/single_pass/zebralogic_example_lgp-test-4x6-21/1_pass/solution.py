import itertools
import json

def solve_puzzle():
    # Define the attributes
    houses = [1, 2, 3, 4]
    names = ["Peter", "Arnold", "Alice", "Eric"]
    flowers = ["roses", "daffodils", "carnations", "lilies"]
    hobbies = ["photography", "painting", "cooking", "gardening"]
    pets = ["dog", "fish", "bird", "cat"]
    colors = ["red", "yellow", "green", "white"]
    house_styles = ["craftsman", "colonial", "ranch", "victorian"]

    # Generate all possible permutations
    all_permutations = list(itertools.permutations(names))
    all_permutations += list(itertools.permutations(flowers))
    all_permutations += list(itertools.permutations(hobbies))
    all_permutations += list(itertools.permutations(pets))
    all_permutations += list(itertools.permutations(colors))
    all_permutations += list(itertools.permutations(house_styles))

    # Iterate over all possible combinations
    for names_perm in all_permutations[::6]:
        for flowers_perm in all_permutations[1::6]:
            for hobbies_perm in all_permutations[2::6]:
                for pets_perm in all_permutations[3::6]:
                    for colors_perm in all_permutations[4::6]:
                        for house_styles_perm in all_permutations[5::6]:
                            # Create a dictionary to store the current combination
                            current_solution = {
                                house: {
                                    "Name": names_perm[i],
                                    "Flower": flowers_perm[i],
                                    "Hobby": hobbies_perm[i],
                                    "Pet": pets_perm[i],
                                    "Color": colors_perm[i],
                                    "House Style": house_styles_perm[i]
                                } for i, house in enumerate(houses)
                            }

                            # Check all the clues
                            if (current_solution[2]["Name"] == "Arnold" and
                                current_solution[2]["House Style"] == "craftsman" and
                                names_perm.index("Peter") < flowers_perm.index("roses") and
                                hobbies_perm.index("photography") == pets_perm.index("dog") and
                                flowers_perm.index("daffodils") != 3 and
                                flowers_perm.index("roses") == colors_perm.index("red") and
                                colors_perm.index("red") == house_styles_perm.index("colonial") and
                                pets_perm.index("fish") == colors_perm.index("white") and
                                colors_perm.index("red") < hobbies_perm.index("cooking") and
                                colors_perm.index("white") == flowers_perm.index("carnations") and
                                colors_perm.index("white") > hobbies_perm.index("gardening") and
                                flowers_perm.index("daffodils") == colors_perm.index("yellow") and
                                current_solution[4]["Name"] == "Eric" and
                                current_solution[4]["Pet"] == "cat"):
                                
                                # If all clues are satisfied, format the solution
                                solution_rows = []
                                for house in houses:
                                    row = [str(house)] + [
                                        current_solution[house][attr] for attr in 
                                        ["Name", "Flower", "Hobby", "Pet", "Color", "House Style"]
                                    ]
                                    solution_rows.append(row)

                                solution_dict = {
                                    "solution": {
                                        "header": ["House", "Name", "Flower", "Hobby", "Pet", "Color", "House Style"],
                                        "rows": solution_rows
                                    }
                                }

                                # Output the solution as JSON
                                print(json.dumps(solution_dict, indent=2))
                                return

# Run the solver
solve_puzzle()