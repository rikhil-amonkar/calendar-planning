import itertools
import json

def main():
    # Define the attributes and their possible values
    names = ['Eric', 'Arnold']
    children = ['Bella', 'Fred']
    lunches = ['grilled cheese', 'pizza']
    
    solution_found = None
    
    # Generate all permutations for each attribute
    for name_perm in itertools.permutations(names):
        for child_perm in itertools.permutations(children):
            for lunch_perm in itertools.permutations(lunches):
                # Create assignment for the two houses
                house1 = [1, name_perm[0], child_perm[0], lunch_perm[0]]
                house2 = [2, name_perm[1], child_perm[1], lunch_perm[1]]
                assignment = [house1, house2]
                
                valid = True
                
                # Check Constraint 1: Pizza eater is Arnold
                pizza_house = None
                for house in assignment:
                    if house[3] == 'pizza':
                        pizza_house = house
                        break
                if pizza_house is None or pizza_house[1] != 'Arnold':
                    valid = False
                    continue  # Skip to next permutation if invalid
                
                # Check Constraint 2: Grilled cheese eater is directly left of Fred's child
                gc_house = None
                for house in assignment:
                    if house[3] == 'grilled cheese':
                        gc_house = house
                        break
                if gc_house is None:
                    valid = False
                else:
                    idx = assignment.index(gc_house)
                    if idx == 0:  # Grilled cheese in house1
                        if assignment[1][2] != 'Fred':  # Check house2's child
                            valid = False
                    else:  # Grilled cheese in house2 (no house to the right)
                        valid = False
                
                if valid:
                    solution_found = assignment
                    break  # Break out of innermost loop
            if solution_found is not None:
                break
        if solution_found is not None:
            break
    
    # Prepare the output
    if solution_found is None:
        result = {"solution": {}}
    else:
        header = ["House", "Name", "Child", "Lunch"]
        rows = []
        for house in solution_found:
            rows.append([str(attr) for attr in house])
        result = {
            "solution": {
                "header": header,
                "rows": rows
            }
        }
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()