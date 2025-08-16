#!/usr/bin/env python3
import itertools
import json

def solve():
    houses = [1, 2]
    names = ["Eric", "Arnold"]
    house_styles = ["victorian", "colonial"]
    
    # Generate all permutations for names and house styles
    for perm_names in itertools.permutations(names, len(houses)):
        for perm_styles in itertools.permutations(house_styles, len(houses)):
            # Constraint 2: Eric is in the first house
            if perm_names[0] != "Eric":
                continue
            
            # Constraint 1: The Victorian house is somewhere to the left of the Colonial house.
            try:
                index_victorian = perm_styles.index("victorian")
                index_colonial = perm_styles.index("colonial")
            except ValueError:
                continue
                
            if index_victorian < index_colonial:
                # Build solution rows in the required order.
                solution_rows = []
                for i in range(len(houses)):
                    solution_rows.append([str(houses[i]), perm_names[i], perm_styles[i]])
                return solution_rows
    return []

def main():
    solution = solve()
    output = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": solution
        }
    }
    print(json.dumps(output))

if __name__ == '__main__':
    main()