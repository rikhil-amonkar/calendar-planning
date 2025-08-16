import json

def main():
    # Define the attributes
    names = ['Arnold', 'Eric']
    vacations = ['beach', 'mountain']
    
    # Generate all possible assignments
    candidates = []
    for name1 in names:
        name2 = next(n for n in names if n != name1)
        for vac1 in vacations:
            vac2 = next(v for v in vacations if v != vac1)
            candidate = [
                {'House': '1', 'Name': name1, 'Vacation': vac1},
                {'House': '2', 'Name': name2, 'Vacation': vac2}
            ]
            candidates.append(candidate)
    
    # Find the solution that satisfies the constraints
    solution_candidate = None
    for candidate in candidates:
        # Check if Arnold and beach are in the same house
        same_house = False
        for house in candidate:
            if house['Name'] == 'Arnold' and house['Vacation'] == 'beach':
                same_house = True
                break
        if same_house:
            continue
        
        # Get the house numbers for Arnold and beach
        beach_house_num = None
        arnold_house_num = None
        for house in candidate:
            if house['Vacation'] == 'beach':
                beach_house_num = int(house['House'])
            if house['Name'] == 'Arnold':
                arnold_house_num = int(house['House'])
        
        if beach_house_num is None or arnold_house_num is None:
            continue
        
        # Check if Arnold is to the right of the beach lover
        if arnold_house_num > beach_house_num:
            solution_candidate = candidate
            break
    
    # Prepare the output
    if solution_candidate is None:
        print(json.dumps({"solution": {}}))
    else:
        rows = []
        for house in solution_candidate:
            row = [house['House'], house['Name'], house['Vacation']]
            rows.append(row)
        
        output = {
            "solution": {
                "header": ["House", "Name", "Vacation"],
                "rows": rows
            }
        }
        print(json.dumps(output))

if __name__ == "__main__":
    main()