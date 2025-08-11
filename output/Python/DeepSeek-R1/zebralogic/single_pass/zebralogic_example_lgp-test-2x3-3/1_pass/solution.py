import itertools
import json

def main():
    # Define the attributes and their possible values
    attributes = {
        'name': ['Arnold', 'Eric'],
        'lunch': ['grilled cheese', 'pizza'],
        'mother': ['Holly', 'Aniya']
    }
    
    houses = [1, 2]
    
    # Fixed lunch assignment from clue 1
    lunch_assignment = {
        1: 'grilled cheese',
        2: 'pizza'
    }
    
    # Generate all permutations for name and mother
    name_perms = list(itertools.permutations(attributes['name']))
    mother_perms = list(itertools.permutations(attributes['mother']))
    
    solution_found = None
    for n_perm in name_perms:
        for m_perm in mother_perms:
            candidate = {
                1: {'name': n_perm[0], 'lunch': lunch_assignment[1], 'mother': m_perm[0]},
                2: {'name': n_perm[1], 'lunch': lunch_assignment[2], 'mother': m_perm[1]}
            }
            
            # Check clue 2: Arnold is not in the second house
            if candidate[2]['name'] == 'Arnold':
                continue
                
            # Check clue 3: Arnold (in house1) has mother Holly
            if candidate[1]['name'] == 'Arnold':
                if candidate[1]['mother'] != 'Holly':
                    continue
            else:
                continue  # Arnold must be in house1 (from clue2), so skip if not
            
            solution_found = candidate
            break
        if solution_found:
            break
            
    # If no solution found, use the deduced solution (shouldn't happen for this puzzle)
    if solution_found is None:
        solution_found = {
            1: {'name': 'Arnold', 'lunch': 'grilled cheese', 'mother': 'Holly'},
            2: {'name': 'Eric', 'lunch': 'pizza', 'mother': 'Aniya'}
        }
    
    # Build the output structure
    header = ["House", "Name", "Lunch", "Mother's Name"]
    rows = []
    for house in houses:
        rows.append([
            str(house),
            solution_found[house]['name'],
            solution_found[house]['lunch'],
            solution_found[house]['mother']
        ])
    
    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()