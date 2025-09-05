import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values for each category
    names = ['Eric', 'Peter', 'Arnold']
    mothers = ['Holly', 'Aniya', 'Janelle']
    foods = ['pizza', 'grilled cheese', 'spaghetti']
    houses = [1, 2, 3]
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for mother_perm in permutations(mothers):
            for food_perm in permutations(foods):
                # Create assignment dictionaries
                assignment = {}
                for i, house in enumerate(houses):
                    assignment[house] = {
                        'Name': name_perm[i],
                        'Mother': mother_perm[i],
                        'Food': food_perm[i]
                    }
                
                # Check all constraints
                valid = True
                
                # Clue 2: The person who loves eating grilled cheese is directly left of 
                # The person whose mother's name is Aniya
                grilled_cheese_house = None
                aniya_mother_house = None
                
                for house in houses:
                    if assignment[house]['Food'] == 'grilled cheese':
                        grilled_cheese_house = house
                    if assignment[house]['Mother'] == 'Aniya':
                        aniya_mother_house = house
                
                if grilled_cheese_house is None or aniya_mother_house is None:
                    valid = False
                elif grilled_cheese_house + 1 != aniya_mother_house:
                    valid = False
                
                # Clue 3: The person who loves eating grilled cheese is Eric
                if grilled_cheese_house is not None:
                    if assignment[grilled_cheese_house]['Name'] != 'Eric':
                        valid = False
                
                # Clue 4: Peter is The person whose mother's name is Holly
                peter_house = None
                holly_mother_house = None
                
                for house in houses:
                    if assignment[house]['Name'] == 'Peter':
                        peter_house = house
                    if assignment[house]['Mother'] == 'Holly':
                        holly_mother_house = house
                
                if peter_house is None or holly_mother_house is None:
                    valid = False
                elif peter_house != holly_mother_house:
                    valid = False
                
                # Clue 1: The person who loves the spaghetti eater and Peter are next to each other
                spaghetti_house = None
                for house in houses:
                    if assignment[house]['Food'] == 'spaghetti':
                        spaghetti_house = house
                
                if spaghetti_house is not None and peter_house is not None:
                    if abs(spaghetti_house - peter_house) != 1:
                        valid = False
                
                # If all constraints are satisfied, return the solution
                if valid:
                    result = {
                        "solution": {
                            "header": ["House", "Name", "Mother", "Food"],
                            "rows": []
                        }
                    }
                    
                    for house in sorted(assignment.keys()):
                        row = [
                            str(house),
                            assignment[house]['Name'],
                            assignment[house]['Mother'],
                            assignment[house]['Food']
                        ]
                        result["solution"]["rows"].append(row)
                    
                    return result
    
    return None

def main():
    solution = solve_puzzle()
    if solution:
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"solution": {"header": [], "rows": []}}, indent=2))

if __name__ == "__main__":
    main()