import json

def main():
    # Define the attributes and their possible values
    attributes = {
        'Name': ['Arnold', 'Eric'],
        'Education': ['associate', 'high school'],
        'Height': ['short', 'very short'],
        'Lunch': ['grilled cheese', 'pizza'],
        'Drink': ['tea', 'water']
    }
    
    # Generate all permutations for each attribute
    perms = {}
    for attr, values in attributes.items():
        perms[attr] = [
            (values[0], values[1]),
            (values[1], values[0])
        ]
    
    # Iterate over all possible combinations
    solution_found = None
    for name_perm in perms['Name']:
        for edu_perm in perms['Education']:
            for height_perm in perms['Height']:
                for lunch_perm in perms['Lunch']:
                    for drink_perm in perms['Drink']:
                        candidate = {
                            'Name': name_perm,
                            'Education': edu_perm,
                            'Height': height_perm,
                            'Lunch': lunch_perm,
                            'Drink': drink_perm
                        }
                        if check_candidate(candidate):
                            solution_found = candidate
                            break
                    if solution_found:
                        break
                if solution_found:
                    break
            if solution_found:
                break
        if solution_found:
            break
    
    # Format the solution
    if solution_found:
        header = ["House", "Name", "Education", "Height", "Lunch", "Drink"]
        rows = []
        for i in range(2):
            house_attrs = [
                str(i+1),
                solution_found['Name'][i],
                solution_found['Education'][i],
                solution_found['Height'][i],
                solution_found['Lunch'][i],
                solution_found['Drink'][i]
            ]
            rows.append(house_attrs)
        
        result = {
            "solution": {
                "header": header,
                "rows": rows
            }
        }
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

def check_candidate(candidate):
    # Clue 1: very short iff pizza
    for i in range(2):
        if (candidate['Height'][i] == 'very short') != (candidate['Lunch'][i] == 'pizza'):
            return False
    
    # Clue 2: grilled cheese in second house
    if candidate['Lunch'][1] != 'grilled cheese':
        return False
    
    # Clue 3: high school iff pizza
    for i in range(2):
        if (candidate['Education'][i] == 'high school') != (candidate['Lunch'][i] == 'pizza'):
            return False
    
    # Clue 4: tea iff grilled cheese
    for i in range(2):
        if (candidate['Drink'][i] == 'tea') != (candidate['Lunch'][i] == 'grilled cheese'):
            return False
    
    # Clue 5: Arnold iff pizza
    for i in range(2):
        if (candidate['Name'][i] == 'Arnold') != (candidate['Lunch'][i] == 'pizza'):
            return False
    
    return True

if __name__ == "__main__":
    main()