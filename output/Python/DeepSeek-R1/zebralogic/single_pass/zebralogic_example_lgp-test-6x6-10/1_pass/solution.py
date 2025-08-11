import json

class ContradictionError(Exception):
    pass

def assign_value(domains, attr, house, value):
    if domains[attr][house] == {value}:
        return False
    if len(domains[attr][house]) == 1:
        current_val = next(iter(domains[attr][house]))
        if current_val != value:
            raise ContradictionError(f"House {house} {attr} is already {current_val}, cannot assign {value}")
    domains[attr][house] = {value}
    return True

def remove_value(domains, attr, house, value):
    if value not in domains[attr][house]:
        return False
    domains[attr][house].discard(value)
    if len(domains[attr][house]) == 0:
        raise ContradictionError(f"Domain for house {house} {attr} is empty after removing {value}")
    return True

def apply_same_house(domains, attr1, val1, attr2, val2):
    changed = False
    for i in range(6):
        if val1 in domains[attr1][i] and len(domains[attr1][i]) == 1:
            changed |= assign_value(domains, attr2, i, val2)
        if val2 in domains[attr2][i] and len(domains[attr2][i]) == 1:
            changed |= assign_value(domains, attr1, i, val1)
    
    for i in range(6):
        if val1 not in domains[attr1][i] and val2 in domains[attr2][i]:
            if remove_value(domains, attr2, i, val2):
                changed = True
        if val2 not in domains[attr2][i] and val1 in domains[attr1][i]:
            if remove_value(domains, attr1, i, val1):
                changed = True
    return changed

def apply_direct_neighbor(domains, attrA, valA, attrB, valB, offset):
    changed = False
    for i in range(6):
        j = i + offset
        if j < 0 or j >= 6:
            continue
        if valA in domains[attrA][i] and len(domains[attrA][i]) == 1:
            changed |= assign_value(domains, attrB, j, valB)
        if valB in domains[attrB][j] and len(domains[attrB][j]) == 1:
            changed |= assign_value(domains, attrA, i, valA)
    
    for i in range(6):
        j = i + offset
        if j < 0 or j >= 6:
            if 0 <= i < 6:
                if valA in domains[attrA][i]:
                    if remove_value(domains, attrA, i, valA):
                        changed = True
            continue
        if valA in domains[attrA][i] and valB not in domains[attrB][j]:
            if remove_value(domains, attrA, i, valA):
                changed = True
        if valB in domains[attrB][j] and valA not in domains[attrA][i]:
            if remove_value(domains, attrB, j, valB):
                changed = True
    return changed

def apply_left_of(domains, attrA, valA, attrB, valB):
    changed = False
    possible_A = [i for i in range(6) if valA in domains[attrA][i]]
    possible_B = [i for i in range(6) if valB in domains[attrB][i]]
    if not possible_A or not possible_B:
        return changed
    minB = min(possible_B)
    maxA = max(possible_A)
    for i in range(minB, 6):
        if valA in domains[attrA][i]:
            if remove_value(domains, attrA, i, valA):
                changed = True
    for j in range(0, maxA+1):
        if valB in domains[attrB][j]:
            if remove_value(domains, attrB, j, valB):
                changed = True
    return changed

def apply_all_constraints(domains, same_house_constraints, direct_neighbor_constraints, left_of_constraints):
    changed = True
    while changed:
        changed = False
        for constr in same_house_constraints:
            attr1, val1, attr2, val2 = constr
            if apply_same_house(domains, attr1, val1, attr2, val2):
                changed = True
        for constr in direct_neighbor_constraints:
            attrA, valA, attrB, valB, offset = constr
            if apply_direct_neighbor(domains, attrA, valA, attrB, valB, offset):
                changed = True
        for constr in left_of_constraints:
            attrA, valA, attrB, valB = constr
            if apply_left_of(domains, attrA, valA, attrB, valB):
                changed = True
        
        changed_inner = True
        while changed_inner:
            changed_inner = False
            for attr in domains:
                for i in range(6):
                    if len(domains[attr][i]) == 1:
                        val = next(iter(domains[attr][i]))
                        for j in range(6):
                            if j != i and val in domains[attr][j]:
                                domains[attr][j].discard(val)
                                changed_inner = True
                                changed = True
    return

def main():
    attributes = ['name', 'lunch', 'height', 'drink', 'pet', 'phone']
    name_vals = ['Arnold', 'Bob', 'Peter', 'Alice', 'Carol', 'Eric']
    lunch_vals = ['stew', 'grilled cheese', 'stir fry', 'soup', 'pizza', 'spaghetti']
    height_vals = ['tall', 'average', 'super tall', 'very short', 'very tall', 'short']
    drink_vals = ['root beer', 'boba tea', 'coffee', 'water', 'tea', 'milk']
    pet_vals = ['hamster', 'fish', 'cat', 'dog', 'bird', 'rabbit']
    phone_vals = ['samsung galaxy s21', 'xiaomi mi 11', 'google pixel 6', 'iphone 13', 'huawei p50', 'oneplus 9']
    
    domains = {
        'name': [set(name_vals) for _ in range(6)],
        'lunch': [set(lunch_vals) for _ in range(6)],
        'height': [set(height_vals) for _ in range(6)],
        'drink': [set(drink_vals) for _ in range(6)],
        'pet': [set(pet_vals) for _ in range(6)],
        'phone': [set(phone_vals) for _ in range(6)]
    }
    
    same_house_constraints = [
        ('name', 'Bob', 'height', 'tall'),
        ('lunch', 'stir fry', 'drink', 'milk'),
        ('lunch', 'grilled cheese', 'height', 'tall'),
        ('phone', 'xiaomi mi 11', 'drink', 'coffee'),
        ('phone', 'oneplus 9', 'name', 'Arnold'),
        ('height', 'super tall', 'pet', 'fish'),
        ('pet', 'fish', 'name', 'Alice'),
        ('phone', 'samsung galaxy s21', 'name', 'Carol'),
        ('lunch', 'pizza', 'height', 'short'),
        ('name', 'Arnold', 'height', 'very tall'),
        ('lunch', 'spaghetti', 'phone', 'google pixel 6'),
        ('height', 'very short', 'lunch', 'spaghetti'),
        ('pet', 'dog', 'drink', 'milk')
    ]
    
    direct_neighbor_constraints = [
        ('drink', 'root beer', 'phone', 'xiaomi mi 11', 1),
        ('phone', 'huawei p50', 'lunch', 'grilled cheese', 1),
        ('drink', 'tea', 'lunch', 'pizza', 1),
        ('pet', 'fish', 'name', 'Eric', 1)
    ]
    
    left_of_constraints = [
        ('phone', 'google pixel 6', 'pet', 'hamster'),
        ('height', 'super tall', 'name', 'Peter'),
        ('pet', 'bird', 'lunch', 'spaghetti')
    ]
    
    try:
        assign_value(domains, 'phone', 2, 'iphone 13')
        assign_value(domains, 'lunch', 1, 'soup')
        remove_value(domains, 'pet', 4, 'rabbit')
        remove_value(domains, 'pet', 4, 'hamster')
        remove_value(domains, 'height', 1, 'very tall')
        remove_value(domains, 'drink', 0, 'boba tea')
        remove_value(domains, 'drink', 1, 'boba tea')
        remove_value(domains, 'drink', 5, 'root beer')
        remove_value(domains, 'phone', 0, 'xiaomi mi 11')
        remove_value(domains, 'phone', 5, 'huawei p50')
        remove_value(domains, 'lunch', 0, 'grilled cheese')
        remove_value(domains, 'drink', 5, 'tea')
        remove_value(domains, 'lunch', 0, 'pizza')
        remove_value(domains, 'pet', 5, 'fish')
        remove_value(domains, 'name', 0, 'Eric')
        
        apply_all_constraints(domains, same_house_constraints, direct_neighbor_constraints, left_of_constraints)
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Lunch", "Height", "Drink", "Pet", "Phone"],
                "rows": []
            }
        }
        
        for i in range(6):
            house_num = str(i+1)
            row = [house_num]
            for attr in attributes:
                if len(domains[attr][i]) != 1:
                    raise Exception(f"House {i+1} {attr} has domain size {len(domains[attr][i])}: {domains[attr][i]}")
                val = next(iter(domains[attr][i]))
                row.append(val)
            solution['solution']['rows'].append(row)
        
        print(json.dumps(solution, indent=2))
        
    except ContradictionError as e:
        print(f"Contradiction: {e}")
    except Exception as e:
        print(f"Error: {e}")

if __name__ == '__main__':
    main()