import json

def main():
    attributes = ['Name', 'Food', 'CarModel', 'PhoneModel', 'Occupation', 'Drink']
    domains = {
        'Name': {'Eric', 'Peter', 'Arnold', 'Alice', 'Bob'},
        'Food': {'stir fry', 'spaghetti', 'stew', 'grilled cheese', 'pizza'},
        'CarModel': {'ford f150', 'tesla model 3', 'bmw 3 series', 'toyota camry', 'honda civic'},
        'PhoneModel': {'iphone 13', 'google pixel 6', 'samsung galaxy s21', 'oneplus 9', 'huawei p50'},
        'Occupation': {'teacher', 'lawyer', 'doctor', 'artist', 'engineer'},
        'Drink': {'tea', 'milk', 'water', 'root beer', 'coffee'}
    }
    
    possibilities = {}
    for attr in attributes:
        possibilities[attr] = [set(domains[attr]) for _ in range(5)]
    
    def clue1():
        for i in range(5):
            if 'root beer' in possibilities['Drink'][i]:
                if 'honda civic' not in possibilities['CarModel'][i]:
                    possibilities['Drink'][i].discard('root beer')
            if 'honda civic' in possibilities['CarModel'][i]:
                if 'root beer' not in possibilities['Drink'][i]:
                    possibilities['CarModel'][i].discard('honda civic')
    
    def clue2():
        for i in range(4):
            if 'milk' in possibilities['Drink'][i]:
                if 'grilled cheese' not in possibilities['Food'][i+1]:
                    possibilities['Drink'][i].discard('milk')
            if 'grilled cheese' in possibilities['Food'][i+1]:
                if 'milk' not in possibilities['Drink'][i]:
                    possibilities['Food'][i+1].discard('grilled cheese')
    
    def clue3_4_14():
        for i in range(5):
            if 'Alice' in possibilities['Name'][i]:
                if 'samsung galaxy s21' not in possibilities['PhoneModel'][i]:
                    possibilities['Name'][i].discard('Alice')
                else:
                    possibilities['PhoneModel'][i] = {'samsung galaxy s21'}
                if 'stir fry' not in possibilities['Food'][i]:
                    possibilities['Name'][i].discard('Alice')
                else:
                    possibilities['Food'][i] = {'stir fry'}
                if 'artist' not in possibilities['Occupation'][i]:
                    possibilities['Name'][i].discard('Alice')
                else:
                    possibilities['Occupation'][i] = {'artist'}
        for i in range(5):
            if 'samsung galaxy s21' in possibilities['PhoneModel'][i]:
                if 'Alice' not in possibilities['Name'][i]:
                    possibilities['PhoneModel'][i].discard('samsung galaxy s21')
            if 'stir fry' in possibilities['Food'][i]:
                if 'Alice' not in possibilities['Name'][i]:
                    possibilities['Food'][i].discard('stir fry')
            if 'artist' in possibilities['Occupation'][i]:
                if 'Alice' not in possibilities['Name'][i]:
                    possibilities['Occupation'][i].discard('artist')
    
    def clue5():
        if 'tea' in possibilities['Drink'][4]:
            possibilities['Drink'][4].discard('tea')
    
    def clue6():
        for i in range(5):
            if 'bmw 3 series' in possibilities['CarModel'][i]:
                found = False
                for j in range(i+1, 5):
                    if 'tea' in possibilities['Drink'][j]:
                        found = True
                        break
                if not found:
                    possibilities['CarModel'][i].discard('bmw 3 series')
        for j in range(5):
            if 'tea' in possibilities['Drink'][j]:
                found = False
                for i in range(0, j):
                    if 'bmw 3 series' in possibilities['CarModel'][i]:
                        found = True
                        break
                if not found:
                    possibilities['Drink'][j].discard('tea')
    
    def clue7():
        for i in range(5):
            if 'Arnold' in possibilities['Name'][i]:
                if 'doctor' not in possibilities['Occupation'][i]:
                    possibilities['Name'][i].discard('Arnold')
                else:
                    possibilities['Occupation'][i] = {'doctor'}
            if 'doctor' in possibilities['Occupation'][i]:
                if 'Arnold' not in possibilities['Name'][i]:
                    possibilities['Occupation'][i].discard('doctor')
    
    def clue8():
        for i in range(5):
            if 'iphone 13' in possibilities['PhoneModel'][i]:
                if 'coffee' not in possibilities['Drink'][i]:
                    possibilities['PhoneModel'][i].discard('iphone 13')
            if 'coffee' in possibilities['Drink'][i]:
                if 'iphone 13' not in possibilities['PhoneModel'][i]:
                    possibilities['Drink'][i].discard('coffee')
    
    def clue9():
        for i in range(5):
            if 'engineer' in possibilities['Occupation'][i]:
                if 'bmw 3 series' not in possibilities['CarModel'][i]:
                    possibilities['Occupation'][i].discard('engineer')
            if 'bmw 3 series' in possibilities['CarModel'][i]:
                if 'engineer' not in possibilities['Occupation'][i]:
                    possibilities['CarModel'][i].discard('bmw 3 series')
    
    def clue10():
        for i in range(5):
            if 'stew' in possibilities['Food'][i]:
                if 'iphone 13' not in possibilities['PhoneModel'][i]:
                    possibilities['Food'][i].discard('stew')
            if 'iphone 13' in possibilities['PhoneModel'][i]:
                if 'stew' not in possibilities['Food'][i]:
                    possibilities['PhoneModel'][i].discard('iphone 13')
    
    def clue11():
        for i in range(4):
            if 'Arnold' in possibilities['Name'][i]:
                if 'oneplus 9' not in possibilities['PhoneModel'][i+1]:
                    possibilities['Name'][i].discard('Arnold')
                if 'lawyer' not in possibilities['Occupation'][i+1]:
                    possibilities['Name'][i].discard('Arnold')
            if 'oneplus 9' in possibilities['PhoneModel'][i+1]:
                if 'Arnold' not in possibilities['Name'][i]:
                    possibilities['PhoneModel'][i+1].discard('oneplus 9')
            if 'lawyer' in possibilities['Occupation'][i+1]:
                if 'Arnold' not in possibilities['Name'][i]:
                    possibilities['Occupation'][i+1].discard('lawyer')
    
    def clue12():
        for i in range(4):
            if 'honda civic' in possibilities['CarModel'][i]:
                if 'spaghetti' not in possibilities['Food'][i+1]:
                    possibilities['CarModel'][i].discard('honda civic')
            if 'spaghetti' in possibilities['Food'][i+1]:
                if 'honda civic' not in possibilities['CarModel'][i]:
                    possibilities['Food'][i+1].discard('spaghetti')
    
    def clue13():
        for i in range(5):
            if 'google pixel 6' in possibilities['PhoneModel'][i]:
                if 'tea' not in possibilities['Drink'][i]:
                    possibilities['PhoneModel'][i].discard('google pixel 6')
            if 'tea' in possibilities['Drink'][i]:
                if 'google pixel 6' not in possibilities['PhoneModel'][i]:
                    possibilities['Drink'][i].discard('tea')
    
    def clue15():
        for i in range(5):
            if 'Alice' in possibilities['Name'][i]:
                possible = False
                if i <= 2 and 'ford f150' in possibilities['CarModel'][i+2]:
                    possible = True
                if i >= 2 and 'ford f150' in possibilities['CarModel'][i-2]:
                    possible = True
                if not possible:
                    possibilities['Name'][i].discard('Alice')
        for j in range(5):
            if 'ford f150' in possibilities['CarModel'][j]:
                possible = False
                if j >= 2 and 'Alice' in possibilities['Name'][j-2]:
                    possible = True
                if j <= 2 and 'Alice' in possibilities['Name'][j+2]:
                    possible = True
                if not possible:
                    possibilities['CarModel'][j].discard('ford f150')
    
    def clue16():
        for i in range(5):
            if 'Arnold' in possibilities['Name'][i]:
                if 'toyota camry' not in possibilities['CarModel'][i]:
                    possibilities['Name'][i].discard('Arnold')
                else:
                    possibilities['CarModel'][i] = {'toyota camry'}
            if 'toyota camry' in possibilities['CarModel'][i]:
                if 'Arnold' not in possibilities['Name'][i]:
                    possibilities['CarModel'][i].discard('toyota camry')
    
    def clue17():
        if 'Eric' in possibilities['Name'][3]:
            possibilities['Name'][3] = {'Eric'}
        for i in range(5):
            if i != 3 and 'Eric' in possibilities['Name'][i]:
                possibilities['Name'][i].discard('Eric')
    
    def clue18():
        for i in range(5):
            if 'oneplus 9' in possibilities['PhoneModel'][i]:
                if 'lawyer' not in possibilities['Occupation'][i]:
                    possibilities['PhoneModel'][i].discard('oneplus 9')
            if 'lawyer' in possibilities['Occupation'][i]:
                if 'oneplus 9' not in possibilities['PhoneModel'][i]:
                    possibilities['Occupation'][i].discard('lawyer')
    
    def clue19():
        for i in range(5):
            if 'grilled cheese' in possibilities['Food'][i]:
                if 'Peter' not in possibilities['Name'][i]:
                    possibilities['Food'][i].discard('grilled cheese')
            if 'Peter' in possibilities['Name'][i]:
                if 'grilled cheese' not in possibilities['Food'][i]:
                    possibilities['Name'][i].discard('Peter')
    
    constraint_funcs = [
        clue1, clue2, clue3_4_14, clue5, clue6, clue7, clue8, clue9, clue10,
        clue11, clue12, clue13, clue15, clue16, clue17, clue18, clue19
    ]
    
    changed = True
    while changed:
        old_possibilities = {}
        for attr in attributes:
            old_possibilities[attr] = [set(house_set) for house_set in possibilities[attr]]
        
        for func in constraint_funcs:
            func()
        
        for attr in attributes:
            for i in range(5):
                if len(possibilities[attr][i]) == 1:
                    val = next(iter(possibilities[attr][i]))
                    for j in range(5):
                        if j != i and val in possibilities[attr][j]:
                            possibilities[attr][j].discard(val)
        
        changed = False
        for attr in attributes:
            for i in range(5):
                if possibilities[attr][i] != old_possibilities[attr][i]:
                    changed = True
                    break
            if changed:
                break
    
    rows = []
    for i in range(5):
        row = [str(i+1)]
        for attr in attributes:
            if len(possibilities[attr][i]) == 1:
                row.append(next(iter(possibilities[attr][i])))
            else:
                raise RuntimeError(f"House {i+1} has multiple possibilities for {attr}: {possibilities[attr][i]}")
        rows.append(row)
    
    solution_dict = {
        "solution": {
            "header": ["House", "Name", "Food", "CarModel", "PhoneModel", "Occupation", "Drink"],
            "rows": rows
        }
    }
    
    print(json.dumps(solution_dict))

if __name__ == '__main__':
    main()