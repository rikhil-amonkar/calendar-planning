import itertools
import json

def main():
    attributes = ['Name', 'Flower', 'Hobby', 'Pet', 'Color', 'HouseStyle']
    domains = {
        'Name': ['Peter', 'Arnold', 'Alice', 'Eric'],
        'Flower': ['roses', 'daffodils', 'carnations', 'lilies'],
        'Hobby': ['photography', 'painting', 'cooking', 'gardening'],
        'Pet': ['dog', 'fish', 'bird', 'cat'],
        'Color': ['red', 'yellow', 'green', 'white'],
        'HouseStyle': ['craftsman', 'colonial', 'ranch', 'victorian']
    }
    
    same_house_constraints = [
        ('HouseStyle', 'craftsman', 'Name', 'Arnold'),
        ('Flower', 'roses', 'Color', 'red'),
        ('Hobby', 'photography', 'Pet', 'dog'),
        ('Flower', 'daffodils', 'Color', 'yellow'),
        ('HouseStyle', 'colonial', 'Color', 'red'),
        ('Pet', 'fish', 'Color', 'white'),
        ('Color', 'white', 'Flower', 'carnations'),
        ('Name', 'Eric', 'HouseStyle', 'victorian'),
        ('Name', 'Eric', 'Pet', 'cat')
    ]
    
    relative_constraints = [
        (('Flower', 'roses'), ('Name', 'Peter'), 'right'),
        (('Hobby', 'cooking'), ('Color', 'red'), 'right'),
        (('Color', 'white'), ('Hobby', 'gardening'), 'right')
    ]
    
    def check_house(house_i):
        for (a1, v1, a2, v2) in same_house_constraints:
            if a1 in house_i and house_i[a1] == v1:
                if a2 in house_i and house_i[a2] != v2:
                    return False
            if a2 in house_i and house_i[a2] == v2:
                if a1 in house_i and house_i[a1] != v1:
                    return False
        return True

    def check_constraints(positions, up_to_house):
        if 'daffodils' in positions['Flower'] and positions['Flower']['daffodils'] == 3:
            return False
        
        for (a1, v1, a2, v2) in same_house_constraints:
            if v1 in positions[a1] and v2 in positions[a2]:
                if positions[a1][v1] != positions[a2][v2]:
                    return False
                    
        for ((a1, v1), (a2, v2), rel) in relative_constraints:
            if v1 in positions[a1] and v2 in positions[a2]:
                if rel == 'right':
                    if positions[a1][v1] <= positions[a2][v2]:
                        return False
        return True

    houses = [None] * 4
    available = {attr: set(domains[attr]) for attr in attributes}
    positions = {attr: {} for attr in attributes}
    
    def backtrack(i):
        if i == 4:
            return houses[:]
        
        if i == 1:
            if 'Arnold' not in available['Name'] or 'craftsman' not in available['HouseStyle']:
                return None
            house_i = {'Name': 'Arnold', 'HouseStyle': 'craftsman'}
            available['Name'].remove('Arnold')
            available['HouseStyle'].remove('craftsman')
            other_attrs = ['Flower', 'Hobby', 'Pet', 'Color']
            values_list = [list(available[attr]) for attr in other_attrs]
            for values in itertools.product(*values_list):
                for idx, attr in enumerate(other_attrs):
                    house_i[attr] = values[idx]
                if not check_house(house_i):
                    continue
                for idx, attr in enumerate(other_attrs):
                    available[attr].remove(values[idx])
                for attr in other_attrs:
                    positions[attr][house_i[attr]] = i
                positions['Name']['Arnold'] = i
                positions['HouseStyle']['craftsman'] = i
                houses[i] = house_i
                if check_constraints(positions, i):
                    res = backtrack(i+1)
                    if res is not None:
                        return res
                houses[i] = None
                for attr in other_attrs:
                    if house_i[attr] in positions[attr]:
                        del positions[attr][house_i[attr]]
                positions['Name'].pop('Arnold', None)
                positions['HouseStyle'].pop('craftsman', None)
                for idx, attr in enumerate(other_attrs):
                    available[attr].add(values[idx])
            available['Name'].add('Arnold')
            available['HouseStyle'].add('craftsman')
            return None
        else:
            other_attrs = attributes
            values_list = [list(available[attr]) for attr in other_attrs]
            for values in itertools.product(*values_list):
                house_i = dict(zip(other_attrs, values))
                if not check_house(house_i):
                    continue
                for attr, val in zip(other_attrs, values):
                    available[attr].remove(val)
                for attr, val in zip(other_attrs, values):
                    positions[attr][val] = i
                houses[i] = house_i
                if check_constraints(positions, i):
                    res = backtrack(i+1)
                    if res is not None:
                        return res
                houses[i] = None
                for attr, val in zip(other_attrs, values):
                    available[attr].add(val)
                for attr, val in zip(other_attrs, values):
                    if val in positions[attr]:
                        del positions[attr][val]
            return None

    solution = backtrack(0)
    if solution is None:
        output = {"solution": {"header": ["House", "Name", "Flower", "Hobby", "Pet", "Color", "HouseStyle"], "rows": []}}
        print(json.dumps(output))
        return

    header = ["House", "Name", "Flower", "Hobby", "Pet", "Color", "HouseStyle"]
    rows = []
    for idx, house in enumerate(solution):
        row = [str(idx+1)]
        for attr in header[1:]:
            row.append(house[attr])
        rows.append(row)
    
    output = {"solution": {"header": header, "rows": rows}}
    print(json.dumps(output))

if __name__ == "__main__":
    main()