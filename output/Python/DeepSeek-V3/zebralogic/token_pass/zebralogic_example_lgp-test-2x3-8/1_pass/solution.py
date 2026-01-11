import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values
    names = ["Arnold", "Eric"]
    birthdays = ["april", "sept"]
    mothers = ["Aniya", "Holly"]
    houses = [1, 2]
    
    # Generate all permutations for each attribute across houses
    for name_perm in permutations(names, 2):
        for bday_perm in permutations(birthdays, 2):
            for mother_perm in permutations(mothers, 2):
                # Create assignment mapping
                assignment = {}
                for i in range(2):
                    assignment[houses[i]] = {
                        "Name": name_perm[i],
                        "Birthday": bday_perm[i],
                        "Mother": mother_perm[i]
                    }
                
                # Check clue 1: Eric is somewhere to the left of the person whose mother's name is Holly
                eric_house = None
                holly_house = None
                for house in houses:
                    if assignment[house]["Name"] == "Eric":
                        eric_house = house
                    if assignment[house]["Mother"] == "Holly":
                        holly_house = house
                
                # Both must exist and Eric must be to the left (lower house number)
                if eric_house is None or holly_house is None:
                    continue
                if not (eric_house < holly_house):
                    continue
                
                # Check clue 2: The person whose birthday is in April is in the first house
                if assignment[1]["Birthday"] != "april":
                    continue
                
                # All constraints satisfied - build solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Birthday", "Mother"],
                        "rows": []
                    }
                }
                
                for house in houses:
                    row = [
                        str(house),
                        assignment[house]["Name"],
                        assignment[house]["Birthday"],
                        assignment[house]["Mother"]
                    ]
                    solution["solution"]["rows"].append(row)
                
                return solution
    
    return None

def main():
    result = solve_puzzle()
    if result:
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"error": "No solution found"}, indent=2))

if __name__ == "__main__":
    main()