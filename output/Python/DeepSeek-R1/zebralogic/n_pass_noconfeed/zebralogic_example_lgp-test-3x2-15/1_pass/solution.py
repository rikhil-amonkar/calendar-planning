import itertools
import json

def main():
    houses = [1, 2, 3]
    names = ['Arnold', 'Peter', 'Eric']
    heights = ['short', 'average', 'very short']
    
    # Generate all possible name assignments
    name_perms = list(itertools.permutations(names))
    
    # Apply constraints to find valid assignment
    valid_assignment = None
    for perm in name_perms:
        name_assignment = {house: name for house, name in zip(houses, perm)}
        
        # Check clue 1: Peter is right of Eric
        eric_house = next(house for house, name in name_assignment.items() if name == 'Eric')
        peter_house = next(house for house, name in name_assignment.items() if name == 'Peter')
        if peter_house <= eric_house:
            continue
            
        # Check clue 4: Arnold next to very short (which must be in house 3 due to clues 2 and 3)
        arnold_house = next(house for house, name in name_assignment.items() if name == 'Arnold')
        if abs(arnold_house - 3) != 1:
            continue
            
        valid_assignment = name_assignment
        break
        
    # Build height assignment from clues 2 and 3
    height_assignment = {
        1: 'short',
        2: 'average',
        3: 'very short'
    }
    
    # Prepare solution rows
    rows = []
    for house in houses:
        rows.append([
            str(house),
            valid_assignment[house],
            height_assignment[house]
        ])
        
    # Create solution dictionary
    solution = {
        "solution": {
            "header": ["House", "Name", "Height"],
            "rows": rows
        }
    }
    
    # Output as JSON
    print(json.dumps(solution, indent=2))

if __name__ == "__main__":
    main()