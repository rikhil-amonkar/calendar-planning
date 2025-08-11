import itertools
import json

def check_single_house(house):
    if 'name' in house and house['name'] == 'Eric':
        if 'house_style' in house and house['house_style'] != 'victorian':
            return False
        if 'pet' in house and house['pet'] != 'cat':
            return False
    if 'house_style' in house and house['house_style'] == 'victorian':
        if 'name' in house and house['name'] != 'Eric':
            return False
        if 'pet' in house and house['pet'] != 'cat':
            return False
    if 'pet' in house and house['pet'] == 'cat':
        if 'name' in house and house['name'] != 'Eric':
            return False
        if 'house_style' in house and house['house_style'] != 'victorian':
            return False
    if 'house_style' in house and house['house_style'] == 'colonial':
        if 'color' in house and house['color'] != 'red':
            return False
        if 'flower' in house and house['flower'] != 'roses':
            return False
    if 'color' in house and house['color'] == 'red':
        if 'house_style' in house and house['house_style'] != 'colonial':
            return False
        if 'flower' in house and house['flower'] != 'roses':
            return False
    if 'flower' in house and house['flower'] == 'roses':
        if 'house_style' in house and house['house_style'] != 'colonial':
            return False
        if 'color' in house and house['color'] != 'red':
            return False
    if 'color' in house and house['color'] == 'white':
        if 'flower' in house and house['flower'] != 'carnations':
            return False
        if 'pet' in house and house['pet'] != 'fish':
            return False
    if 'flower' in house and house['flower'] == 'carnations':
        if 'color' in house and house['color'] != 'white':
            return False
        if 'pet' in house and house['pet'] != 'fish':
            return False
    if 'pet' in house and house['pet'] == 'fish':
        if 'color' in house and house['color'] != 'white':
            return False
        if 'flower' in house and house['flower'] != 'carnations':
            return False
    if 'flower' in house and house['flower'] == 'daffodils':
        if 'color' in house and house['color'] != 'yellow':
            return False
    if 'color' in house and house['color'] == 'yellow':
        if 'flower' in house and house['flower'] != 'daffodils':
            return False
    if 'hobby' in house and house['hobby'] == 'photography':
        if 'pet' in house and house['pet'] != 'dog':
            return False
    if 'pet' in house and house['pet'] == 'dog':
        if 'hobby' in house and house['hobby'] != 'photography':
            return False
    return True

def check_global_constraints(state):
    try:
        house_rose = next(i for i, house in enumerate(state) if house['flower'] == 'roses')
        house_peter = next(i for i, house in enumerate(state) if house['name'] == 'Peter')
        if house_rose <= house_peter:
            return False
    except StopIteration:
        return False
    try:
        house_daffodils = next(i for i, house in enumerate(state) if house['flower'] == 'daffodils')
        if house_daffodils == 3:
            return False
    except StopIteration:
        return False
    try:
        house_cooking = next(i for i, house in enumerate(state) if house['hobby'] == 'cooking')
        house_red = next(i for i, house in enumerate(state) if house['color'] == 'red')
        if house_cooking <= house_red:
            return False
    except StopIteration:
        return False
    try:
        house_white = next(i for i, house in enumerate(state) if house['color'] == 'white')
        house_gardening = next(i for i, house in enumerate(state) if house['hobby'] == 'gardening')
        if house_white <= house_gardening:
            return False
    except StopIteration:
        return False
    return True

def backtrack(i, available, state):
    if i == 4:
        if check_global_constraints(state):
            return state
        else:
            return None
    all_attributes = ['name', 'flower', 'hobby', 'pet', 'color', 'house_style']
    assigned_attrs = set(state[i].keys())
    missing_attrs = [attr for attr in all_attributes if attr not in assigned_attrs]
    if not missing_attrs:
        return backtrack(i+1, available, state)
    choices = []
    for attr in missing_attrs:
        choices.append(list(available[attr]))
    found_solution = None
    for values in itertools.product(*choices):
        candidate_house = state[i].copy()
        for idx, attr in enumerate(missing_attrs):
            candidate_house[attr] = values[idx]
        if not check_single_house(candidate_house):
            continue
        new_available = {}
        for key in available:
            new_available[key] = set(available[key])
        for idx, attr in enumerate(missing_attrs):
            val = values[idx]
            if val in new_available[attr]:
                new_available[attr].remove(val)
        new_state = state.copy()
        new_state[i] = candidate_house
        res = backtrack(i+1, new_available, new_state)
        if res is not None:
            found_solution = res
            break
    return found_solution

def main():
    all_attributes = ['name', 'flower', 'hobby', 'pet', 'color', 'house_style']
    state = [dict() for _ in range(4)]
    state[1] = {'name': 'Arnold', 'house_style': 'craftsman'}
    available = {
        'name': set(['Peter', 'Alice', 'Eric']),
        'flower': set(['roses', 'daffodils', 'carnations', 'lilies']),
        'hobby': set(['photography', 'painting', 'cooking', 'gardening']),
        'pet': set(['dog', 'fish', 'bird', 'cat']),
        'color': set(['red', 'yellow', 'green', 'white']),
        'house_style': set(['colonial', 'ranch', 'victorian'])
    }
    solution_state = backtrack(0, available, state)
    if solution_state is None:
        print('No solution found')
        return
    header = ["House", "Name", "Flower", "Hobby", "Pet", "Color", "House Style"]
    rows = []
    for i, house in enumerate(solution_state):
        row = [
            str(i+1),
            house['name'],
            house['flower'],
            house['hobby'],
            house['pet'],
            house['color'],
            house['house_style']
        ]
        rows.append(row)
    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(output))

if __name__ == "__main__":
    main()