import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Bob", "Peter", "Alice", "Eric", "Carol", "Arnold"]
    vacations = ["mountain", "camping", "cruise", "city", "cultural", "beach"]

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for vacation_perm in itertools.permutations(vacations):
            # Create a dictionary to map house number to attributes
            house_map = {house: {"Name": name, "Vacation": vacation} 
                         for house, name, vacation in zip(houses, name_perm, vacation_perm)}

            # Check all constraints
            if (house_map[3]["Vacation"] == "cultural" and
                house_map[3]["Name"] == "Peter" and
                house_map[2]["Name"] == "Eric" and
                house_map.index(house_map[next(house for house in houses if house_map[house]["Name"] == "Alice")]) < 
                house_map.index(house_map[next(house for house in houses if house_map[house]["Name"] == "Eric")]) and
                house_map[1]["Name"] != "Bob" and
                house_map[house_map.index(house_map[next(house for house in houses if house_map[house]["Name"] == "Bob")]) + 1]["Name"] == "Arnold" and
                house_map[next(house for house in houses if house_map[house]["Vacation"] == "beach")]["House"] > 
                house_map[next(house for house in houses if house_map[house]["Vacation"] == "cultural")]["House"] and
                house_map[next(house for house in houses if house_map[house]["Vacation"] == "cruise")]["Name"] == "Bob" and
                house_map[4]["Vacation"] == "city"):
                
                # Prepare the solution in the required format
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Vacation"],
                        "rows": [[str(house), house_map[house]["Name"], house_map[house]["Vacation"]] for house in houses]
                    }
                }
                return json.dumps(solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())