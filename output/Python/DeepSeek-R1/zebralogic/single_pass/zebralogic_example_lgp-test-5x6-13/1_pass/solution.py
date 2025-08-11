import json

def same_house_constraint(attrs, attr1, val1, attr2, val2):
    changed = False
    for i in range(5):
        if val1 in attrs[attr1][i] and val2 not in attrs[attr2][i]:
            attrs[attr1][i].remove(val1)
            changed = True
        if val2 in attrs[attr2][i] and val1 not in attrs[attr1][i]:
            attrs[attr2][i].remove(val2)
            changed = True
    return changed

def left_of(attrs, attrA, valA, attrB, valB, distance, direct):
    if direct and distance == 1:
        changed = False
        for i in range(4):
            if valA in attrs[attrA][i] and valB not in attrs[attrB][i+1]:
                attrs[attrA][i].remove(valA)
                changed = True
        for j in range(1,5):
            if valB in attrs[attrB][j] and valA not in attrs[attrA][j-1]:
                attrs[attrB][j].remove(valB)
                changed = True
        return changed
    return False

def strictly_left(attrs, attrA, valA, attrB, valB):
    changed = False
    for i in range(5):
        if valA in attrs[attrA][i]:
            found = False
            for j in range(i+1, 5):
                if valB in attrs[attrB][j]:
                    found = True
                    break
            if not found:
                attrs[attrA][i].remove(valA)
                changed = True
    for j in range(5):
        if valB in attrs[attrB][j]:
            found = False
            for i in range(j):
                if valA in attrs[attrA][i]:
                    found = True
                    break
            if not found:
                attrs[attrB][j].remove(valB)
                changed = True
    return changed

def distance_constraint(attrs, attr1, val1, attr2, val2, d):
    changed = False
    for i in range(5):
        if val1 in attrs[attr1][i]:
            poss = []
            if i - d >= 0:
                poss.append(i - d)
            if i + d < 5:
                poss.append(i + d)
            found = False
            for j in poss:
                if val2 in attrs[attr2][j]:
                    found = True
                    break
            if not found and poss:
                attrs[attr1][i].remove(val1)
                changed = True
    for j in range(5):
        if val2 in attrs[attr2][j]:
            poss = []
            if j - d >= 0:
                poss.append(j - d)
            if j + d < 5:
                poss.append(j + d)
            found = False
            for i in poss:
                if val1 in attrs[attr1][i]:
                    found = True
                    break
            if not found and poss:
                attrs[attr2][j].remove(val2)
                changed = True
    return changed

def unary_assign(attrs, attr, index, value):
    changed = False
    if attrs[attr][index] != set([value]):
        attrs[attr][index] = set([value])
        changed = True
    for i in range(5):
        if i != index and value in attrs[attr][i]:
            attrs[attr][i].remove(value)
            changed = True
    return changed

def unary_remove(attrs, attr, index, value):
    if value in attrs[attr][index]:
        attrs[attr][index].remove(value)
        return True
    return False

def reduce_attributes(attrs):
    changed = False
    for attr in attrs:
        for i in range(5):
            if len(attrs[attr][i]) == 1:
                val = next(iter(attrs[attr][i]))
                for j in range(5):
                    if j != i and val in attrs[attr][j]:
                        attrs[attr][j].remove(val)
                        changed = True
    return changed

attrs = {
    'Name': [set(['Eric','Peter','Arnold','Alice','Bob']) for _ in range(5)],
    'Lunch': [set(['stir fry','spaghetti','stew','grilled cheese','pizza']) for _ in range(5)],
    'Car': [set(['ford f150','tesla model 3','bmw 3 series','toyota camry','honda civic']) for _ in range(5)],
    'Phone': [set(['iphone 13','google pixel 6','samsung galaxy s21','oneplus 9','huawei p50']) for _ in range(5)],
    'Occupation': [set(['teacher','lawyer','doctor','artist','engineer']) for _ in range(5)],
    'Drink': [set(['tea','milk','water','root beer','coffee']) for _ in range(5)]
}

constraints = [
    lambda a: unary_assign(a, 'Name', 3, 'Eric'),
    lambda a: unary_remove(a, 'Drink', 4, 'tea'),
    lambda a: same_house_constraint(a, 'Drink', 'root beer', 'Car', 'honda civic'),
    lambda a: same_house_constraint(a, 'Name', 'Alice', 'Phone', 'samsung galaxy s21'),
    lambda a: same_house_constraint(a, 'Name', 'Alice', 'Lunch', 'stir fry'),
    lambda a: same_house_constraint(a, 'Name', 'Arnold', 'Occupation', 'doctor'),
    lambda a: same_house_constraint(a, 'Phone', 'iphone 13', 'Drink', 'coffee'),
    lambda a: same_house_constraint(a, 'Occupation', 'engineer', 'Car', 'bmw 3 series'),
    lambda a: same_house_constraint(a, 'Lunch', 'stew', 'Phone', 'iphone 13'),
    lambda a: same_house_constraint(a, 'Phone', 'google pixel 6', 'Drink', 'tea'),
    lambda a: same_house_constraint(a, 'Name', 'Alice', 'Occupation', 'artist'),
    lambda a: same_house_constraint(a, 'Name', 'Arnold', 'Car', 'toyota camry'),
    lambda a: same_house_constraint(a, 'Phone', 'oneplus 9', 'Occupation', 'lawyer'),
    lambda a: same_house_constraint(a, 'Name', 'Peter', 'Lunch', 'grilled cheese'),
    lambda a: left_of(a, 'Drink', 'milk', 'Lunch', 'grilled cheese', 1, True),
    lambda a: strictly_left(a, 'Car', 'bmw 3 series', 'Drink', 'tea'),
    lambda a: left_of(a, 'Occupation', 'doctor', 'Phone', 'oneplus 9', 1, True),
    lambda a: left_of(a, 'Car', 'honda civic', 'Lunch', 'spaghetti', 1, True),
    lambda a: distance_constraint(a, 'Name', 'Alice', 'Car', 'ford f150', 2)
]

changed = True
while changed:
    changed = reduce_attributes(attrs)
    for constr in constraints:
        changed = constr(attrs) or changed

solved = True
for attr in attrs:
    for i in range(5):
        if len(attrs[attr][i]) != 1:
            solved = False
            break
    if not solved:
        break

if not solved:
    raise Exception("Not solved!")

rows = []
for i in range(5):
    row = [str(i+1)]
    row.append(next(iter(attrs['Name'][i])))
    row.append(next(iter(attrs['Lunch'][i])))
    row.append(next(iter(attrs['Car'][i])))
    row.append(next(iter(attrs['Phone'][i])))
    row.append(next(iter(attrs['Occupation'][i])))
    row.append(next(iter(attrs['Drink'][i])))
    rows.append(row)

result = {
    "solution": {
        "header": ["House", "Name", "Lunch", "Car", "Phone", "Occupation", "Drink"],
        "rows": rows
    }
}

print(json.dumps(result))