import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Carol", "Peter", "Eric", "Arnold", "Alice", "Bob"]
    cigars = ["blends", "yellow monster", "pall mall", "blue master", "dunhill", "prince"]

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for cigar_perm in itertools.permutations(cigars):
            # Unpack permutations for easier access
            name_to_house = {name: house for house, name in zip(houses, name_perm)}
            cigar_to_house = {cigar: house for house, cigar in zip(houses, cigar_perm)}

            # Check each clue
            if (name_to_house["Arnold"] < cigar_to_house["blends"] and
                cigar_to_house["blue master"] == 5 and
                name_to_house["Arnold"] < cigar_to_house["prince"] and
                abs(cigar_to_house["yellow monster"] - cigar_to_house["blends"]) == 2 and
                cigar_to_house["pall mall"] == 3 and
                name_to_house["Eric"] == 6 and
                abs(name_to_house["Carol"] - name_to_house["Eric"]) == 1 and
                name_to_house["Peter"] == 1 and
                name_to_house["Bob"] == 3):

                # If all clues are satisfied, construct the solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Cigar"],
                        "rows": []
                    }
                }

                for house in houses:
                    name = name_perm[house - 1]
                    cigar = cigar_perm[house - 1]
                    solution["solution"]["rows"].append([str(house), name, cigar])

                return json.dumps(solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())