import json
from itertools import permutations

def solve_puzzle():
    # Define the attributes
    names = ["Arnold", "Eric"]
    vacations = ["beach", "mountain"]
    houses = [1, 2]
    
    # Generate all possible permutations for names and vacations
    for name_perm in permutations(names):
        for vacation_perm in permutations(vacations):
            # Create assignment for each house
            assignment = []
            for i in range(len(houses)):
                assignment.append({
                    "house": houses[i],
                    "name": name_perm[i],
                    "vacation": vacation_perm[i]
                })
            
            # Check clue 1: Arnold is somewhere to the right of the person who loves beach vacations
            beach_lover_house = None
            arnold_house = None
            
            for house in assignment:
                if house["vacation"] == "beach":
                    beach_lover_house = house["house"]
                if house["name"] == "Arnold":
                    arnold_house = house["house"]
            
            # Arnold must be to the right of beach lover (higher house number)
            if arnold_house > beach_lover_house:
                # Found valid solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Vacation"],
                        "rows": []
                    }
                }
                
                for house in sorted(assignment, key=lambda x: x["house"]):
                    solution["solution"]["rows"].append([
                        str(house["house"]),
                        house["name"],
                        house["vacation"]
                    ])
                
                return solution
    
    return None

def main():
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))

if __name__ == "__main__":
    main()