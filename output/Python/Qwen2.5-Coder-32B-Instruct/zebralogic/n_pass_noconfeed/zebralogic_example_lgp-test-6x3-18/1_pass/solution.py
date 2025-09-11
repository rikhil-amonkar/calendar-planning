import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Arnold", "Eric", "Bob", "Alice", "Carol", "Peter"]
    mothers = ["Sarah", "Holly", "Janelle", "Aniya", "Penny", "Kailyn"]
    pets = ["hamster", "dog", "bird", "cat", "fish", "rabbit"]

    # Generate all possible permutations for names, mothers, and pets
    for name_perm in itertools.permutations(names):
        for mother_perm in itertools.permutations(mothers):
            for pet_perm in itertools.permutations(pets):
                # Create a dictionary to store the current permutation
                assignment = {house: {"Name": name_perm[i], "Mother": mother_perm[i], "Pet": pet_perm[i]} for i, house in enumerate(houses)}

                # Check all constraints
                if (assignment[1]["Name"] != "Bob" and  # Constraint 1
                    abs(name_perm.index("Eric") - pet_perm.index("rabbit")) == 2 and  # Constraint 2
                    name_perm.index("Arnold") == pet_perm.index("cat") and  # Constraint 10
                    name_perm.index("Arnold") + 1 == mothers.index("Holly") and  # Constraint 3 & 7
                    name_perm.index("Arnold") + 1 == pet_perm.index("rabbit") - 1 and  # Constraint 4
                    name_perm.index("Arnold") + 1 == pet_perm.index("rabbit") - 1 and  # Constraint 4
                    abs(pet_perm.index("dog") - pet_perm.index("cat")) == 2 and  # Constraint 6
                    name_perm.index("Alice") + 1 == name_perm.index("Carol") and  # Constraint 8
                    name_perm.index("Carol") == mothers.index("Aniya") and  # Constraint 9
                    name_perm.index("Eric") == pet_perm.index("rabbit") and  # Constraint 5
                    mothers.index("Kailyn") == pet_perm.index("rabbit") and  # Constraint 11
                    mothers.index("Sarah") == pet_perm.index("fish")):  # Constraint 12

                    # If all constraints are satisfied, format the solution
                    solution_rows = [[str(house), assignment[house]["Name"], assignment[house]["Mother"], assignment[house]["Pet"]] for house in houses]
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Mother", "Pet"],
                            "rows": solution_rows
                        }
                    }
                    return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())