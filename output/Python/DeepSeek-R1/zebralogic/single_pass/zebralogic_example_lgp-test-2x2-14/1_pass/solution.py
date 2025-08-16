import json

def main():
    # Define the houses and attributes
    houses = [1, 2]
    names = ['Eric', 'Arnold']
    foods = ['pizza', 'grilled cheese']
    
    # Generate all possible assignments
    possibilities = []
    for name1 in names:
        for food1 in foods:
            # House 2 gets the remaining name and food
            name2 = next(n for n in names if n != name1)
            food2 = next(f for f in foods if f != food1)
            candidate = {
                1: {'Name': name1, 'Food': food1},
                2: {'Name': name2, 'Food': food2}
            }
            possibilities.append(candidate)
    
    # Apply clues to filter possibilities
    valid_candidates = []
    for candidate in possibilities:
        # Clue 1: Pizza lover is in house 2
        if candidate[2]['Food'] != 'pizza':
            continue
        # Clue 2: Arnold is not in house 1
        if candidate[1]['Name'] == 'Arnold':
            continue
        valid_candidates.append(candidate)
    
    # There should be exactly one valid solution
    if len(valid_candidates) != 1:
        raise RuntimeError("No unique solution found")
    
    solution = valid_candidates[0]
    
    # Build the output structure
    output = {
        "solution": {
            "header": ["House", "Name", "Food"],
            "rows": []
        }
    }
    
    # Add rows in house order
    for house in houses:
        row = [str(house)]
        row.append(solution[house]['Name'])
        row.append(solution[house]['Food'])
        output['solution']['rows'].append(row)
    
    # Output as JSON
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()