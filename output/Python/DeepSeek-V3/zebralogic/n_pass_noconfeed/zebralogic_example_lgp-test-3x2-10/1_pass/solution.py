import json
from itertools import permutations

def solve_puzzle():
    # Define the domain of possible values
    names = ['Eric', 'Arnold', 'Peter']
    heights = ['short', 'very short', 'average']
    houses = [1, 2, 3]
    
    # Generate all possible permutations for names and heights
    name_perms = permutations(names)
    height_perms = permutations(heights)
    
    # Try all combinations of name and height assignments
    for name_assignment in name_perms:
        for height_assignment in height_perms:
            # Create assignment dictionaries
            assignment = {}
            for i, house in enumerate(houses):
                assignment[house] = {
                    'Name': name_assignment[i],
                    'Height': height_assignment[i]
                }
            
            # Check all constraints
            valid = True
            
            # Clue 1: Eric is not in the first house
            if assignment[1]['Name'] == 'Eric':
                valid = False
            
            # Clue 2: The person who is very short is somewhere to the left of the person who is short
            very_short_house = None
            short_house = None
            for house in houses:
                if assignment[house]['Height'] == 'very short':
                    very_short_house = house
                if assignment[house]['Height'] == 'short':
                    short_house = house
            
            if very_short_house is None or short_house is None or very_short_house >= short_house:
                valid = False
            
            # Clue 3: The person who is very short is Eric
            if very_short_house is not None and assignment[very_short_house]['Name'] != 'Eric':
                valid = False
            
            # Clue 4: Arnold is not in the first house
            if assignment[1]['Name'] == 'Arnold':
                valid = False
            
            # If all constraints are satisfied, return the solution
            if valid:
                return assignment
    
    return None

def main():
    solution = solve_puzzle()
    
    if solution:
        # Prepare the output in the required JSON format
        output = {
            "solution": {
                "header": ["House", "Name", "Height"],
                "rows": []
            }
        }
        
        for house in sorted(solution.keys()):
            row = [str(house), solution[house]['Name'], solution[house]['Height']]
            output["solution"]["rows"].append(row)
        
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"solution": {"header": ["House", "Name", "Height"], "rows": []}}))

if __name__ == "__main__":
    main()