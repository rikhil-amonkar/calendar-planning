import json
import itertools

def solve_puzzle():
    houses = [1, 2, 3, 4]
    names = ["Arnold", "Peter", "Eric", "Alice"]
    styles = ["victorian", "ranch", "colonial", "craftsman"]
    
    # Iterate over all possible assignments for names and house styles.
    for perm_names in itertools.permutations(names):
        # Constraint 3: Eric is in the third house.
        if perm_names[2] != "Eric":
            continue
        # Constraint 4: Arnold is in the fourth house.
        if perm_names[3] != "Arnold":
            continue
        
        for perm_styles in itertools.permutations(styles):
            # Constraint 1: Eric is in a Craftsman-style house.
            if perm_styles[2] != "craftsman":
                continue
            
            # Constraint 2: The person in a ranch-style home is directly left of the person residing in a Victorian house.
            adjacent_found = False
            for i in range(len(perm_styles) - 1):
                if perm_styles[i] == "ranch" and perm_styles[i+1] == "victorian":
                    adjacent_found = True
                    break
            if not adjacent_found:
                continue
            
            # Constraint 5: The person residing in a Victorian house is Alice.
            if "victorian" in perm_styles:
                index_victorian = perm_styles.index("victorian")
                if perm_names[index_victorian] != "Alice":
                    continue
            else:
                continue
            
            # If all constraints are met, build and return the solution.
            solution = []
            for i in range(4):
                house_number = str(houses[i])
                solution.append([house_number, perm_names[i], perm_styles[i]])
            return solution
    return None

def main():
    solution_rows = solve_puzzle()
    output = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": solution_rows if solution_rows is not None else []
        }
    }
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()