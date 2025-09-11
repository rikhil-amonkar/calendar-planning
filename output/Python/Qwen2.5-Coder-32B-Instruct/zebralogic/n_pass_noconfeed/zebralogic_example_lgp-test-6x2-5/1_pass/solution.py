import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Bob", "Peter", "Alice", "Eric", "Carol", "Arnold"]
    vacations = ["mountain", "camping", "cruise", "city", "cultural", "beach"]

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for vacation_perm in itertools.permutations(vacations):
            # Unpack permutations for easier access
            house_to_name = dict(zip(houses, name_perm))
            house_to_vacation = dict(zip(houses, vacation_perm))

            # Check all constraints
            if (house_to_vacation[3] == "cultural" and
                house_to_name[3] == "Peter" and
                house_to_vacation[4] == "city" and
                house_to_name[2] == "Eric" and
                house_to_name[1] == "Bob" and house_to_name[2] == "Arnold" and
                house_to_vacation.index("beach") > house_to_vacation.index("cultural") and
                house_to_vacation.index("camping") != 0 and
                house_to_name.index("Eric") > house_to_name.index("Alice")):

                # Construct the solution in the required format
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Vacation"],
                        "rows": []
                    }
                }

                for house in houses:
                    solution["solution"]["rows"].append([
                        str(house),
                        house_to_name[house],
                        house_to_vacation[house]
                    ])

                return json.dumps(solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())