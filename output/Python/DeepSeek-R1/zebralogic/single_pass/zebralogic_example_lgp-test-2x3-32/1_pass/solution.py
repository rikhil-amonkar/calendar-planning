import json

def main():
    attributes = {
        'Name': ['Eric', 'Arnold'],
        'Birthday month': ['april', 'sept'],
        'Favorite color': ['yellow', 'red']
    }
    houses = [1, 2]
    
    domains = {}
    for house in houses:
        domains[house] = {}
        for attr, values in attributes.items():
            domains[house][attr] = set(values)
    
    # Apply clue 2: April birthday in first house
    domains[1]['Birthday month'] = {'april'}
    domains[2]['Birthday month'] = domains[2]['Birthday month'] - {'april'}
    
    # Apply clue 3: Yellow not in first house
    domains[1]['Favorite color'] = {'red'}
    domains[2]['Favorite color'] = {'yellow'}
    
    # Apply clue 1: Eric loves yellow -> must be in house with yellow (house2)
    domains[2]['Name'] = {'Eric'}
    domains[1]['Name'] = domains[1]['Name'] - {'Eric'}
    
    header = ['House', 'Name', 'Birthday month', 'Favorite color']
    rows = []
    for house in houses:
        row = [str(house)]
        for attr in ['Name', 'Birthday month', 'Favorite color']:
            value = next(iter(domains[house][attr]))
            row.append(value)
        rows.append(row)
    
    solution_dict = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(solution_dict))

if __name__ == '__main__':
    main()