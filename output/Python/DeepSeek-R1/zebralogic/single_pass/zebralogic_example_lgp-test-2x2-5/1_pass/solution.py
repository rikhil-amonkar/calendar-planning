import json
from itertools import permutations

def main():
    # Define puzzle parameters
    houses = [1, 2]
    names = ['Eric', 'Arnold']
    house_styles = ['victorian', 'colonial']
    
    # Fixed assignment from clue 2: Eric is in house 1
    name_assignment = {1: 'Eric', 2: 'Arnold'}
    
    # Generate permutations for house styles
    style_permutations = list(permutations(house_styles))
    valid_style_assignment = None
    
    # Check clue 1: Victorian left of Colonial
    for perm in style_permutations:
        victorian_house = None
        colonial_house = None
        
        # Map styles to houses
        for idx, style in enumerate(perm):
            house_num = idx + 1
            if style == 'victorian':
                victorian_house = house_num
            elif style == 'colonial':
                colonial_house = house_num
        
        # Verify constraint
        if victorian_house is not None and colonial_house is not None:
            if victorian_house < colonial_house:
                valid_style_assignment = perm
                break
    
    # Build solution rows
    rows = []
    for house in houses:
        row = [str(house), name_assignment[house], valid_style_assignment[house-1]]
        rows.append(row)
    
    # Construct output dictionary
    output = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": rows
        }
    }
    
    # Output as JSON
    print(json.dumps(output))

if __name__ == "__main__":
    main()