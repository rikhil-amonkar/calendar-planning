import json

def main():
    houses = [1, 2, 3]
    attributes = ['Name', 'BookGenre', 'Smoothie', 'Birthday', 'Height']
    values = {
        'Name': ['Peter', 'Arnold', 'Eric'],
        'BookGenre': ['science fiction', 'mystery', 'romance'],
        'Smoothie': ['watermelon', 'desert', 'cherry'],
        'Birthday': ['april', 'jan', 'sept'],
        'Height': ['average', 'very short', 'short']
    }
    
    domains = {}
    for house in houses:
        domains[house] = {}
        for attr in attributes:
            domains[house][attr] = set(values[attr])
    
    # Apply unary constraints
    domains[1]['Name'] = set(['Eric'])
    domains[2]['Smoothie'].discard('cherry')
    domains[1]['Birthday'].discard('jan')
    
    constraints = [
        ('Name', 'Arnold', 'BookGenre', 'mystery'),
        ('Height', 'very short', 'BookGenre', 'romance'),
        ('BookGenre', 'mystery', 'Birthday', 'sept'),
        ('Height', 'average', 'Smoothie', 'desert'),
        ('Smoothie', 'watermelon', 'Height', 'short'),
        ('Name', 'Eric', 'Smoothie', 'watermelon')
    ]
    
    def must_be_same(domains, houses, attr1, val1, attr2, val2):
        changed = False
        for house in houses:
            if val1 in domains[house][attr1]:
                if val2 not in domains[house][attr2]:
                    domains[house][attr1].discard(val1)
                    changed = True
                else:
                    if len(domains[house][attr2]) > 1:
                        domains[house][attr2] = set([val2])
                        changed = True
            if val2 in domains[house][attr2]:
                if val1 not in domains[house][attr1]:
                    domains[house][attr2].discard(val2)
                    changed = True
                else:
                    if len(domains[house][attr1]) > 1:
                        domains[house][attr1] = set([val1])
                        changed = True
        return changed

    def enforce_uniqueness(domains, houses, attributes):
        changed = False
        for attr in attributes:
            fixed_values = {}
            for house in houses:
                if len(domains[house][attr]) == 1:
                    val = next(iter(domains[house][attr]))
                    if val not in fixed_values:
                        fixed_values[val] = house
            for val, fixed_house in fixed_values.items():
                for house in houses:
                    if house != fixed_house and val in domains[house][attr]:
                        domains[house][attr].discard(val)
                        changed = True
        return changed

    changed = True
    while changed:
        changed = False
        changed_uniqueness = enforce_uniqueness(domains, houses, attributes)
        changed = changed or changed_uniqueness
        for constr in constraints:
            a1, v1, a2, v2 = constr
            changed_constraint = must_be_same(domains, houses, a1, v1, a2, v2)
            changed = changed or changed_constraint

    solution_rows = []
    for house in sorted(houses):
        row = [str(house)]
        for attr in attributes:
            if len(domains[house][attr]) == 1:
                val = next(iter(domains[house][attr]))
                row.append(val)
            else:
                val = next(iter(domains[house][attr]))
                row.append(val)
        solution_rows.append(row)
    
    result = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Smoothie", "Birthday", "Height"],
            "rows": solution_rows
        }
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()