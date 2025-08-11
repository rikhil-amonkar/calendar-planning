import itertools
import json

def main():
    houses = [1, 2]
    attributes = ['Name', 'Lunch']
    domains = {
        'Name': ['Eric', 'Arnold'],
        'Lunch': ['pizza', 'grilled cheese']
    }
    
    perms = {}
    for attr in attributes:
        perms[attr] = list(itertools.permutations(domains[attr]))
    
    solutions = []
    for name_perm in perms['Name']:
        for lunch_perm in perms['Lunch']:
            assignment = {}
            for idx, house in enumerate(houses):
                assignment[house] = {
                    'Name': name_perm[idx],
                    'Lunch': lunch_perm[idx]
                }
            if assignment[2]['Lunch'] != 'pizza':
                continue
            if assignment[1]['Name'] == 'Arnold':
                continue
            solutions.append(assignment)
    
    if solutions:
        sol = solutions[0]
        header = ['House'] + attributes
        rows = []
        for house in houses:
            row = [str(house)]
            for attr in attributes:
                row.append(sol[house][attr])
            rows.append(row)
        result = {
            "solution": {
                "header": header,
                "rows": rows
            }
        }
    else:
        result = {"solution": {"header": [], "rows": []}}
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()