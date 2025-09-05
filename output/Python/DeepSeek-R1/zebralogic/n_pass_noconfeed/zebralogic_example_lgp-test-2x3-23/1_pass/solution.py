import itertools
import json

def main():
    # Define the attributes
    names = ['Eric', 'Arnold']
    children = ['Bella', 'Fred']
    foods = ['grilled cheese', 'pizza']
    houses = [1, 2]
    
    # Generate all possible permutations of attributes for the houses
    for name_perm in itertools.permutations(names):
        for child_perm in itertools.permutations(children):
            for food_perm in itertools.permutations(foods):
                assignment = {
                    1: {'Name': name_perm[0], 'Children': child_perm[0], 'Food': food_perm[0]},
                    2: {'Name': name_perm[1], 'Children': child_perm[1], 'Food': food_perm[1]}
                }
                
                # Check constraints
                valid = True
                
                # Constraint 1: Pizza lover is Arnold
                for house in houses:
                    if assignment[house]['Food'] == 'pizza' and assignment[house]['Name'] != 'Arnold':
                        valid = False
                        break
                if not valid:
                    continue
                    
                # Constraint 2: Grilled cheese eater is left of Fred's parent
                # Since there are only 2 houses, only house 1 can be left of house 2
                if assignment[1]['Food'] == 'grilled cheese':
                    if assignment[2]['Children'] != 'Fred':
                        valid = False
                else:
                    # Grilled cheese must be in house 1 per the constraint
                    valid = False
                    
                if valid:
                    # Prepare the solution in required format
                    rows = []
                    for house in sorted(assignment.keys()):
                        row = [
                            str(house),
                            assignment[house]['Name'],
                            assignment[house]['Children'],
                            assignment[house]['Food']
                        ]
                        rows.append(row)
                    
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Children", "Food"],
                            "rows": rows
                        }
                    }
                    print(json.dumps(solution, indent=2))
                    return
                    
    print("No solution found")

if __name__ == "__main__":
    main()