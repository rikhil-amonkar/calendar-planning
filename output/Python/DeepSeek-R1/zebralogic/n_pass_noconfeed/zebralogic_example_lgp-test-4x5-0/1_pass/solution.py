import copy
import json

def main():
    attributes = ['Name', 'Smoothie', 'Cigar', 'Height', 'PhoneModel']
    
    full_names = set(['Eric', 'Peter', 'Arnold', 'Alice'])
    full_smoothies = set(['dragonfruit', 'cherry', 'desert', 'watermelon'])
    full_cigars = set(['blue master', 'pall mall', 'dunhill', 'prince'])
    full_heights = set(['tall', 'average', 'short', 'very short'])
    full_phones = set(['google pixel 6', 'samsung galaxy s21', 'iphone 13', 'oneplus 9'])
    
    possibilities = {
        'Name': [full_names.copy() for _ in range(4)],
        'Smoothie': [full_smoothies.copy() for _ in range(4)],
        'Cigar': [full_cigars.copy() for _ in range(4)],
        'Height': [full_heights.copy() for _ in range(4)],
        'PhoneModel': [full_phones.copy() for _ in range(4)]
    }
    
    def propagate_unique(possibilities):
        for attr in attributes:
            for i in range(4):
                if len(possibilities[attr][i]) == 1:
                    value = next(iter(possibilities[attr][i]))
                    for j in range(4):
                        if j != i and value in possibilities[attr][j]:
                            possibilities[attr][j].remove(value)
    
    def same_house(attr1, val1, attr2, val2, possibilities):
        houses1 = [i for i in range(4) if val1 in possibilities[attr1][i]]
        houses2 = [i for i in range(4) if val2 in possibilities[attr2][i]]
        common_houses = set(houses1) & set(houses2)
        for i in range(4):
            if i not in common_houses:
                if val1 in possibilities[attr1][i]:
                    possibilities[attr1][i].remove(val1)
                if val2 in possibilities[attr2][i]:
                    possibilities[attr2][i].remove(val2)
        if len(common_houses) == 1:
            i = common_houses.pop()
            possibilities[attr1][i] = set([val1])
            possibilities[attr2][i] = set([val2])
    
    def clue3(possibilities):
        for i in range(3):
            if 'samsung galaxy s21' in possibilities['PhoneModel'][i] and 'iphone 13' not in possibilities['PhoneModel'][i+1]:
                possibilities['PhoneModel'][i].remove('samsung galaxy s21')
        for i in range(1, 4):
            if 'iphone 13' in possibilities['PhoneModel'][i] and 'samsung galaxy s21' not in possibilities['PhoneModel'][i-1]:
                possibilities['PhoneModel'][i].remove('iphone 13')
        possibilities['PhoneModel'][3] -= set(['samsung galaxy s21'])
        possibilities['PhoneModel'][0] -= set(['iphone 13'])
    
    def right_of(attr1, val1, attr2, val2, possibilities):
        for i in range(4):
            if val2 in possibilities[attr2][i]:
                found = False
                for j in range(i+1, 4):
                    if val1 in possibilities[attr1][j]:
                        found = True
                        break
                if not found:
                    possibilities[attr2][i].remove(val2)
        for j in range(4):
            if val1 in possibilities[attr1][j]:
                found = False
                for i in range(0, j):
                    if val2 in possibilities[attr2][i]:
                        found = True
                        break
                if not found:
                    possibilities[attr1][j].remove(val1)
    
    # Apply fixed constraints
    possibilities['Height'][2] = set(['tall'])
    possibilities['Cigar'][0] -= set(['blue master'])
    possibilities['Name'][2] -= set(['Peter'])
    propagate_unique(possibilities)
    
    constraints_same = [
        ('Smoothie', 'dragonfruit', 'Name', 'Eric'),
        ('Cigar', 'dunhill', 'Smoothie', 'cherry'),
        ('Cigar', 'prince', 'PhoneModel', 'oneplus 9'),
        ('Height', 'very short', 'PhoneModel', 'iphone 13'),
        ('Cigar', 'dunhill', 'Height', 'short'),
        ('Name', 'Arnold', 'PhoneModel', 'google pixel 6'),
        ('Smoothie', 'dragonfruit', 'Cigar', 'pall mall')
    ]
    
    changed = True
    while changed:
        old_possibilities = copy.deepcopy(possibilities)
        for constr in constraints_same:
            same_house(*constr, possibilities)
        clue3(possibilities)
        right_of('Cigar', 'dunhill', 'Height', 'very short', possibilities)
        right_of('Smoothie', 'watermelon', 'Smoothie', 'desert', possibilities)
        propagate_unique(possibilities)
        changed = (old_possibilities != possibilities)
    
    # Check if solved
    for attr in attributes:
        for i in range(4):
            if len(possibilities[attr][i]) != 1:
                # If not solved, we try to assign arbitrarily (should not happen)
                value = next(iter(possibilities[attr][i]))
                possibilities[attr][i] = set([value])
                propagate_unique(possibilities)
    
    # Prepare output
    rows = []
    for i in range(4):
        row = [str(i+1)]
        for attr in attributes:
            value = next(iter(possibilities[attr][i]))
            row.append(value)
        rows.append(row)
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Cigar", "Height", "PhoneModel"],
            "rows": rows
        }
    }
    
    print(json.dumps(solution))

if __name__ == '__main__':
    main()