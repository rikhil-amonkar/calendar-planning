import itertools
import json

def main():
    # Define the attributes
    names = ['Arnold', 'Eric']
    foods = ['grilled cheese', 'pizza']
    mothers = ['Holly', 'Aniya']
    houses = [1, 2]
    
    # Generate all possible permutations for each attribute
    solution_found = None
    for name_perm in itertools.permutations(names):
        for food_perm in itertools.permutations(foods):
            for mother_perm in itertools.permutations(mothers):
                assignment = [
                    {'House': houses[0], 'Name': name_perm[0], 'Food': food_perm[0], 'Mother': mother_perm[0]},
                    {'House': houses[1], 'Name': name_perm[1], 'Food': food_perm[1], 'Mother': mother_perm[1]}
                ]
                
                # Apply constraints
                # Constraint 1: Grilled cheese directly left of pizza
                if assignment[0]['Food'] != 'grilled cheese' or assignment[1]['Food'] != 'pizza':
                    continue
                    
                # Constraint 2: Arnold not in second house
                if assignment[1]['Name'] == 'Arnold':
                    continue
                    
                # Constraint 3: Arnold's mother is Holly
                if assignment[0]['Name'] == 'Arnold' and assignment[0]['Mother'] != 'Holly':
                    continue
                if assignment[1]['Name'] == 'Arnold' and assignment[1]['Mother'] != 'Holly':
                    continue
                    
                # If all constraints pass, we found the solution
                solution_found = assignment
                break
            if solution_found:
                break
        if solution_found:
            break
    
    # Prepare the output
    header = ["House", "Name", "Food", "Mother"]
    rows = []
    for house in solution_found:
        rows.append([str(house['House']), house['Name'], house['Food'], house['Mother']])
    
    # Create the result dictionary
    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    
    # Output as JSON
    print(json.dumps(result))

if __name__ == "__main__":
    main()