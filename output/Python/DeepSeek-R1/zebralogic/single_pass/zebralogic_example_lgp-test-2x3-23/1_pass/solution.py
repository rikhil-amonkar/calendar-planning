import itertools
import json

def main():
    names_list = ['Eric', 'Arnold']
    children_list = ['Bella', 'Fred']
    foods_list = ['grilled cheese', 'pizza']
    houses = [1, 2]
    
    found_solution = None
    
    for names in itertools.permutations(names_list):
        for children in itertools.permutations(children_list):
            for foods in itertools.permutations(foods_list):
                assignment = {
                    1: {'Name': names[0], 'Children': children[0], 'Food': foods[0]},
                    2: {'Name': names[1], 'Children': children[1], 'Food': foods[1]}
                }
                
                # Check Clue 1: Pizza eater is Arnold
                clue1_satisfied = True
                for house in houses:
                    if assignment[house]['Food'] == 'pizza':
                        if assignment[house]['Name'] != 'Arnold':
                            clue1_satisfied = False
                            break
                if not clue1_satisfied:
                    continue
                
                # Check Clue 2: Grilled cheese directly left of Fred child
                if assignment[1]['Food'] == 'grilled cheese' and assignment[2]['Children'] == 'Fred':
                    found_solution = assignment
                    break
            if found_solution:
                break
        if found_solution:
            break
    
    if found_solution:
        rows = [
            ["1", found_solution[1]['Name'], found_solution[1]['Children'], found_solution[1]['Food']],
            ["2", found_solution[2]['Name'], found_solution[2]['Children'], found_solution[2]['Food']]
        ]
        output = {
            "solution": {
                "header": ["House", "Name", "Children", "Food"],
                "rows": rows
            }
        }
        print(json.dumps(output))
    else:
        # Fallback in case no solution found (though the puzzle should have one)
        print(json.dumps({"solution": {"header": ["House", "Name", "Children", "Food"], "rows": []}}))

if __name__ == "__main__":
    main()