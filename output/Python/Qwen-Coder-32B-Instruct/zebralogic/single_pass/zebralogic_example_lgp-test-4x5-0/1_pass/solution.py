import itertools
import json

def solve_puzzle():
    # Define the possible values for each attribute
    names = ["Eric", "Peter", "Arnold", "Alice"]
    smoothies = ["dragonfruit", "cherry", "desert", "watermelon"]
    cigars = ["blue master", "pall mall", "dunhill", "prince"]
    heights = ["tall", "average", "short", "very short"]
    phones = ["google pixel 6", "samsung galaxy s21", "iphone 13", "oneplus 9"]

    # Generate all possible permutations for each attribute
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(smoothies)) * \
                       list(itertools.permutations(cigars)) * \
                       list(itertools.permutations(heights)) * \
                       list(itertools.permutations(phones))

    # Define the constraints
    def constraint1(solution):
        return solution["smoothies"].index("dragonfruit") == solution["names"].index("Eric")

    def constraint2(solution):
        return solution["cigars"].index("dunhill") == solution["smoothies"].index("cherry")

    def constraint3(solution):
        return solution["phones"].index("samsung galaxy s21") + 1 == solution["phones"].index("iphone 13")

    def constraint4(solution):
        return solution["cigars"].index("dunhill") > solution["heights"].index("very short")

    def constraint5(solution):
        return solution["smoothies"].index("watermelon") > solution["smoothies"].index("desert")

    def constraint6(solution):
        return solution["cigars"].index("prince") == solution["phones"].index("oneplus 9")

    def constraint7(solution):
        return solution["heights"].index("tall") == 2

    def constraint8(solution):
        return solution["heights"].index("very short") == solution["phones"].index("iphone 13")

    def constraint9(solution):
        return solution["cigars"].index("blue master") != 0

    def constraint10(solution):
        return solution["cigars"].index("dunhill") == solution["heights"].index("short")

    def constraint11(solution):
        return solution["names"].index("Peter") != 2

    def constraint12(solution):
        return solution["phones"].index("google pixel 6") == solution["names"].index("Arnold")

    def constraint13(solution):
        return solution["cigars"].index("pall mall") == solution["smoothies"].index("dragonfruit")

    # Check each permutation to see if it satisfies all constraints
    for names_perm, smoothies_perm, cigars_perm, heights_perm, phones_perm in itertools.product(
            itertools.permutations(names),
            itertools.permutations(smoothies),
            itertools.permutations(cigars),
            itertools.permutations(heights),
            itertools.permutations(phones)
    ):
        solution = {
            "names": names_perm,
            "smoothies": smoothies_perm,
            "cigars": cigars_perm,
            "heights": heights_perm,
            "phones": phones_perm
        }

        if (constraint1(solution) and
            constraint2(solution) and
            constraint3(solution) and
            constraint4(solution) and
            constraint5(solution) and
            constraint6(solution) and
            constraint7(solution) and
            constraint8(solution) and
            constraint9(solution) and
            constraint10(solution) and
            constraint11(solution) and
            constraint12(solution) and
            constraint13(solution)):
            break

    # Format the solution as required
    result = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Cigar", "Height", "Phone"],
            "rows": []
        }
    }

    for i in range(4):
        result["solution"]["rows"].append([
            str(i + 1),
            solution["names"][i],
            solution["smoothies"][i],
            solution["cigars"][i],
            solution["heights"][i],
            solution["phones"][i]
        ])

    return json.dumps(result, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())