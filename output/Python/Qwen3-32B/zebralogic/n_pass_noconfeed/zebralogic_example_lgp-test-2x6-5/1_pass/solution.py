import itertools
import json

def main():
    # Define all attributes and their possible values
    attributes = {
        'Name': ['Arnold', 'Eric'],
        'Occupation': ['engineer', 'doctor'],
        'Birthday': ['april', 'sept'],
        'HouseStyle': ['victorian', 'colonial'],
        'Height': ['very short', 'short'],
        'Cigar': ['pall mall', 'prince']
    }
    
    # Generate all permutations for each attribute
    attr_perms = {}
    for attr, values in attributes.items():
        attr_perms[attr] = list(itertools.permutations(values))
    
    # List of attribute names in order
    attrs_order = list(attributes.keys())
    
    # Iterate through all possible combinations of permutations
    for combo in itertools.product(*[attr_perms[attr] for attr in attrs_order]):
        # Create a dictionary for the current combination
        current_solution = {attr: combo[i] for i, attr in enumerate(attrs_order)}
        
        # Check all constraints
        # Constraint 1: Engineer in first house
        if current_solution['Occupation'][0] != 'engineer':
            continue
        
        # Constraint 6: Engineer is Eric (first house's name is Eric)
        if current_solution['Name'][0] != 'Eric':
            continue
        
        # Constraint 3: Colonial is engineer's house (first house)
        if current_solution['HouseStyle'][0] != 'colonial':
            continue
        
        # Constraint 4: Engineer (house 1) is very short
        if current_solution['Height'][0] != 'very short':
            continue
        
        # Constraint 5: Short (house 2) likes Pall Mall
        if current_solution['Height'][1] == 'short' and current_solution['Cigar'][1] != 'pall mall':
            continue
        
        # Constraint 2: April and doctor are next to each other
        # Doctor is in house 2 (since house 1 is engineer)
        # So April must be in house 1
        if current_solution['Birthday'][0] != 'april':
            continue
        
        # If all constraints are satisfied, build the solution
        solution = {
            "solution": {
                "header": ["House", "Name", "Occupation", "Birthday", "HouseStyle", "Height", "Cigar"],
                "rows": []
            }
        }
        
        # Build rows for house 1 and 2
        for house_num in [1, 2]:
            house_index = 0 if house_num == 1 else 1
            row = [str(house_num)]
            for attr in ["Name", "Occupation", "Birthday", "HouseStyle", "Height", "Cigar"]:
                row.append(current_solution[attr][house_index])
            solution["solution"]["rows"].append(row)
        
        # Output as JSON
        print(json.dumps(solution, indent=2))
        return
    
    # If no solution found (unlikely here)
    print(json.dumps({"error": "No solution found"}, indent=2))

if __name__ == "__main__":
    main()