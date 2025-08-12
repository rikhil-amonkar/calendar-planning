import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Alice", "Bob", "Arnold", "Eric", "Peter"]
    vacations = ["cruise", "city", "camping", "beach", "mountain"]
    children = ["Bella", "Samantha", "Fred", "Meredith", "Timothy"]
    nationalities = ["dane", "norwegian", "brit", "german", "swede"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(vacations)) * \
                       list(itertools.permutations(children)) * \
                       list(itertools.permutations(nationalities))

    # Define the constraints as functions
    def constraint_1(perm):
        return perm[3][4] == "Peter"

    def constraint_2(perm):
        return perm[2][perm[3].index("Bella")] == "Bella"

    def constraint_3(perm):
        samantha_index = perm[2].index("Samantha")
        return samantha_index > 0 and perm[3][samantha_index - 1] == "beach"

    def constraint_4(perm):
        return perm[2][perm[3].index("Bella")] != "Samantha"

    def constraint_5(perm):
        return perm[3][perm[0].index("Alice")] == "brit"

    def constraint_6(perm):
        return perm[3][0] == "cruise"

    def constraint_7(perm):
        return perm[2][3] == "Meredith"

    def constraint_8(perm):
        return perm[0][4] != "Eric"

    def constraint_9(perm):
        norwegian_index = perm[3].index("Peter")
        swede_index = perm[2].index("Bella")
        return swede_index > norwegian_index

    def constraint_10(perm):
        fred_index = perm[2].index("Fred")
        city_index = perm[3].index("city")
        return abs(fred_index - city_index) == 2

    def constraint_11(perm):
        return perm[3][perm[0].index("Bob")] == "camping"

    def constraint_12(perm):
        return perm[3][4] == "dane"

    def constraint_13(perm):
        return perm[0][4] != "Bob"

    # Check all permutations against the constraints
    for perm in itertools.product(*[names, vacations, children, nationalities]):
        if (constraint_1(perm) and constraint_2(perm) and constraint_3(perm) and
            constraint_4(perm) and constraint_5(perm) and constraint_6(perm) and
            constraint_7(perm) and constraint_8(perm) and constraint_9(perm) and
            constraint_10(perm) and constraint_11(perm) and constraint_12(perm) and
            constraint_13(perm)):
            # If all constraints are satisfied, format the solution
            solution = {
                "solution": {
                    "header": ["House", "Name", "Vacation", "Child", "Nationality"],
                    "rows": []
                }
            }
            for i in range(5):
                solution["solution"]["rows"].append([
                    str(i + 1),
                    perm[0][i],
                    perm[1][i],
                    perm[2][i],
                    perm[3][i]
                ])
            return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())