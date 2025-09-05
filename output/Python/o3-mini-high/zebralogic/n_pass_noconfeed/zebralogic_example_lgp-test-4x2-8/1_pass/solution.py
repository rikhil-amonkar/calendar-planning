import itertools
import json

def solve_puzzle():
    houses = ["1", "2", "3", "4"]
    names_list = ["Peter", "Arnold", "Alice", "Eric"]
    colors_list = ["yellow", "green", "red", "white"]
    
    # Iterate over all possible assignments for names and colors
    for names in itertools.permutations(names_list):
        # Constraint 2: Peter is in the first house.
        if names[0] != "Peter":
            continue
        
        # Constraint 4: Arnold is directly left of Eric.
        valid_adjacent = False
        for i in range(len(names) - 1):
            if names[i] == "Arnold" and names[i+1] == "Eric":
                valid_adjacent = True
                break
        if not valid_adjacent:
            continue
        
        for colors in itertools.permutations(colors_list):
            # Constraint 1: The person whose favorite color is green is in the third house.
            if colors[2] != "green":
                continue
            
            # Constraint 5: Eric is the person who loves yellow.
            eric_index = names.index("Eric")
            if colors[eric_index] != "yellow":
                continue
            
            # Constraint 3: There is one house between the person whose favorite color is red and the person who loves yellow.
            red_index = colors.index("red")
            yellow_index = colors.index("yellow")
            if abs(red_index - yellow_index) != 2:
                continue
            
            # All constraints satisfied; build the solution rows.
            solution_rows = []
            for i in range(4):
                solution_rows.append([houses[i], names[i], colors[i]])
            return solution_rows
    return None

if __name__ == "__main__":
    solution = solve_puzzle()
    output = {
        "solution": {
            "header": ["House", "Name", "Color"],
            "rows": solution if solution is not None else []
        }
    }
    print(json.dumps(output, indent=2))