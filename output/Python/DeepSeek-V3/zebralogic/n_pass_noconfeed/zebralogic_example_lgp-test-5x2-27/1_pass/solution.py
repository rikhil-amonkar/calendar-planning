import json
from itertools import permutations

def main():
    # Define all possible values
    names = ["Peter", "Alice", "Bob", "Eric", "Arnold"]
    heights = ["very tall", "average", "tall", "very short", "short"]
    houses = [1, 2, 3, 4, 5]
    
    # Generate all possible permutations of names and heights
    for name_perm in permutations(names):
        for height_perm in permutations(heights):
            # Create assignment dictionaries
            assignment = {}
            for i, house in enumerate(houses):
                assignment[house] = {
                    "name": name_perm[i],
                    "height": height_perm[i]
                }
            
            # Check all constraints
            # Constraint 1: The person who is short is in the second house.
            if assignment[2]["height"] != "short":
                continue
            
            # Constraint 2: Peter is directly left of Bob.
            peter_house = None
            bob_house = None
            for house in houses:
                if assignment[house]["name"] == "Peter":
                    peter_house = house
                if assignment[house]["name"] == "Bob":
                    bob_house = house
            if peter_house is None or bob_house is None or bob_house - peter_house != 1:
                continue
            
            # Constraint 3: Eric is somewhere to the left of Peter.
            eric_house = None
            for house in houses:
                if assignment[house]["name"] == "Eric":
                    eric_house = house
            if eric_house is None or eric_house >= peter_house:
                continue
            
            # Constraint 4: The person who is very tall is directly left of Peter.
            very_tall_house = None
            for house in houses:
                if assignment[house]["height"] == "very tall":
                    very_tall_house = house
            if very_tall_house is None or very_tall_house + 1 != peter_house:
                continue
            
            # Constraint 5: Alice is directly left of the person who has an average height.
            alice_house = None
            average_height_house = None
            for house in houses:
                if assignment[house]["name"] == "Alice":
                    alice_house = house
                if assignment[house]["height"] == "average":
                    average_height_house = house
            if alice_house is None or average_height_house is None or average_height_house - alice_house != 1:
                continue
            
            # Constraint 6: The person who is short and the person who is very short are next to each other.
            short_house = None
            very_short_house = None
            for house in houses:
                if assignment[house]["height"] == "short":
                    short_house = house
                if assignment[house]["height"] == "very short":
                    very_short_house = house
            if short_house is None or very_short_house is None or abs(short_house - very_short_house) != 1:
                continue
            
            # Constraint 7: The person who has an average height is in the fifth house.
            if assignment[5]["height"] != "average":
                continue
            
            # If we reach here, all constraints are satisfied
            # Format the solution
            solution = {
                "solution": {
                    "header": ["House", "Name", "Height"],
                    "rows": []
                }
            }
            
            for house in sorted(assignment.keys()):
                row = [str(house), assignment[house]["name"], assignment[house]["height"]]
                solution["solution"]["rows"].append(row)
            
            # Output the solution as JSON
            print(json.dumps(solution, indent=2))
            return
    
    # If no solution found
    print(json.dumps({"solution": {"header": ["House", "Name", "Height"], "rows": []}}, indent=2))

if __name__ == "__main__":
    main()