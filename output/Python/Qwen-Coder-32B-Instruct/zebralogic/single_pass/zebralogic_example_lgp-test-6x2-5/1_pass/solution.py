import itertools
import json

def solve_puzzle():
    # Define the attributes
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Bob", "Peter", "Alice", "Eric", "Carol", "Arnold"]
    vacations = ["mountain", "camping", "cruise", "city", "cultural", "beach"]

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for vacation_perm in itertools.permutations(vacations):
            # Unpack permutations for easier access
            house_name_map = dict(zip(houses, name_perm))
            house_vacation_map = dict(zip(houses, vacation_perm))

            # Check constraints
            if (house_vacation_map[3] == "cultural" and
                house_vacation_map[3] == "Peter" and
                house_name_map[2] == "Eric" and
                house_name_map[1] == "Alice" and
                house_name_map[3] == "Peter" and
                house_name_map[4] == "Bob" and
                house_vacation_map[4] == "city" and
                house_vacation_map[6] != "camping" and
                house_vacation_map.index("cultural") < house_vacation_map.index("beach") and
                house_name_map[houses[name_perm.index("Bob")]] == "Bob" and
                house_name_map[houses[name_perm.index("Arnold")]] == "Arnold" and
                houses[name_perm.index("Bob")] + 1 == houses[name_perm.index("Arnold")]):
                
                # Construct the solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Vacation"],
                        "rows": []
                    }
                }
                
                for house in houses:
                    solution["solution"]["rows"].append([
                        str(house),
                        house_name_map[house],
                        house_vacation_map[house]
                    ])
                
                return json.dumps(solution, indent=2)

# Output the solution
print(solve_puzzle())