import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values
    names = ["Arnold", "Eric", "Peter", "Alice"]
    occupations = ["doctor", "engineer", "artist", "teacher"]
    houses = [1, 2, 3, 4]
    
    # Generate all possible permutations
    name_perms = list(permutations(names))
    occ_perms = list(permutations(occupations))
    
    # Try all combinations
    for name_assignment in name_perms:
        for occ_assignment in occ_perms:
            # Create house assignments
            assignment = {}
            for i, house in enumerate(houses):
                assignment[house] = {
                    "name": name_assignment[i],
                    "occupation": occ_assignment[i]
                }
            
            # Check all constraints
            valid = True
            
            # Clue 1: There are two houses between Eric and Peter
            eric_house = None
            peter_house = None
            for house, data in assignment.items():
                if data["name"] == "Eric":
                    eric_house = house
                if data["name"] == "Peter":
                    peter_house = house
            
            if eric_house is None or peter_house is None or abs(eric_house - peter_house) != 3:
                valid = False
                continue
            
            # Clue 2: The person who is a teacher is Peter
            for house, data in assignment.items():
                if data["occupation"] == "teacher" and data["name"] != "Peter":
                    valid = False
                    break
            
            if not valid:
                continue
            
            # Clue 3: Peter is not in the first house
            if assignment[1]["name"] == "Peter":
                valid = False
                continue
            
            # Clue 4: There is one house between the person who is a doctor and Alice
            doctor_house = None
            alice_house = None
            for house, data in assignment.items():
                if data["occupation"] == "doctor":
                    doctor_house = house
                if data["name"] == "Alice":
                    alice_house = house
            
            if doctor_house is None or alice_house is None or abs(doctor_house - alice_house) != 2:
                valid = False
                continue
            
            # Clue 5: The person who is an artist is Alice
            for house, data in assignment.items():
                if data["occupation"] == "artist" and data["name"] != "Alice":
                    valid = False
                    break
            
            if valid:
                # Found valid solution
                result = {
                    "solution": {
                        "header": ["House", "Name", "Occupation"],
                        "rows": []
                    }
                }
                
                for house in sorted(assignment.keys()):
                    data = assignment[house]
                    result["solution"]["rows"].append([
                        str(house),
                        data["name"],
                        data["occupation"]
                    ])
                
                return result
    
    return None

# Solve the puzzle and output the result
solution = solve_puzzle()
if solution:
    print(json.dumps(solution, indent=2))
else:
    print(json.dumps({"error": "No solution found"}, indent=2))