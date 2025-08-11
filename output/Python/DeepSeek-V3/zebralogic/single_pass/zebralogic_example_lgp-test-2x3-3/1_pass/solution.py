import json
from itertools import permutations

def solve_puzzle():
    # Define the attributes and their possible values
    attributes = {
        'House': ['1', '2'],
        'Name': ['Arnold', 'Eric'],
        'Lunch': ['grilled cheese', 'pizza'],
        'Mother': ['Holly', 'Aniya']
    }
    
    # Generate all possible permutations for each attribute
    # Since there are only 2 houses, we can pair them directly
    solutions = []
    
    # Iterate through all possible combinations
    for names in permutations(attributes['Name']):
        for lunches in permutations(attributes['Lunch']):
            for mothers in permutations(attributes['Mother']):
                # Create a candidate solution
                candidate = {
                    '1': {
                        'Name': names[0],
                        'Lunch': lunches[0],
                        'Mother': mothers[0]
                    },
                    '2': {
                        'Name': names[1],
                        'Lunch': lunches[1],
                        'Mother': mothers[1]
                    }
                }
                
                # Check all clues
                # Clue 1: grilled cheese is directly left of pizza
                if not (candidate['1']['Lunch'] == 'grilled cheese' and candidate['2']['Lunch'] == 'pizza'):
                    continue
                
                # Clue 2: Arnold is not in the second house
                if candidate['2']['Name'] == 'Arnold':
                    continue
                
                # Clue 3: Arnold's mother is Holly
                # Find Arnold's house
                arnold_house = None
                for house in ['1', '2']:
                    if candidate[house]['Name'] == 'Arnold':
                        arnold_house = house
                        break
                if arnold_house is None:
                    continue  # Arnold must be in one of the houses
                if candidate[arnold_house]['Mother'] != 'Holly':
                    continue
                
                # All clues satisfied, add to solutions
                solutions.append(candidate)
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    # Format the solution as required
    solution = solutions[0]
    header = ['House', 'Name', 'Lunch', 'Mother']
    rows = []
    for house in ['1', '2']:
        row = [house]
        row.append(solution[house]['Name'])
        row.append(solution[house]['Lunch'])
        row.append(solution[house]['Mother'])
        rows.append(row)
    
    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    return result

# Execute and print the result
if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))