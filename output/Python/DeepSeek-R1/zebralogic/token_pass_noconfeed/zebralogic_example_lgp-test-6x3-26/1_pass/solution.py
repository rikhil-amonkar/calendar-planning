import itertools
import json

def main():
    names = ['Alice', 'Eric', 'Bob', 'Peter', 'Arnold', 'Carol']
    heights = ['very tall', 'tall', 'super tall', 'average', 'very short', 'short']
    phones = ['oneplus 9', 'google pixel 6', 'samsung galaxy s21', 'iphone 13', 'huawei p50', 'xiaomi mi 11']
    
    fixed_height = {1: 'super tall', 5: 'very short', 6: 'short'}
    fixed_phone = {4: 'google pixel 6', 5: 'oneplus 9'}
    
    for carol_house in [2, 3]:
        for arnold_house in [2, 3, 4]:
            if arnold_house == carol_house:
                continue
            bob_house = arnold_house - 1
            if bob_house < 1 or bob_house > 6:
                continue
            if bob_house == carol_house or bob_house == arnold_house:
                continue
                
            assigned_names = {
                bob_house: 'Bob',
                arnold_house: 'Arnold',
                carol_house: 'Carol'
            }
            
            remaining_houses = set(range(1, 7)) - {bob_house, arnold_house, carol_house}
            remaining_names = ['Alice', 'Eric', 'Peter']
            
            for name_perm in itertools.permutations(remaining_names):
                name_assignment = assigned_names.copy()
                for house, name in zip(remaining_houses, name_perm):
                    name_assignment[house] = name
                
                height_assignment = fixed_height.copy()
                height_assignment[carol_house] = 'very tall'
                height_assignment[arnold_house] = 'tall'
                
                assigned_height_houses = set(height_assignment.keys())
                if len(assigned_height_houses) < 6:
                    missing_house = (set(range(1, 7)) - assigned_height_houses).pop()
                    height_assignment[missing_house] = 'average'
                
                phone_assignment = fixed_phone.copy()
                phone_assignment[carol_house] = 'xiaomi mi 11'
                
                remaining_phones = set(phones) - set(phone_assignment.values())
                remaining_phone_houses = set(range(1, 7)) - set(phone_assignment.keys())
                
                for phone_perm in itertools.permutations(remaining_phones):
                    for house, phone in zip(remaining_phone_houses, phone_perm):
                        phone_assignment[house] = phone
                    
                    peter_house = None
                    iphone_house = None
                    for house in range(1, 7):
                        if name_assignment[house] == 'Peter':
                            peter_house = house
                        if phone_assignment[house] == 'iphone 13':
                            iphone_house = house
                    if peter_house is None or iphone_house is None:
                        continue
                    if peter_house >= iphone_house:
                        continue
                    
                    if phone_assignment[1] == 'samsung galaxy s21':
                        continue
                    
                    eric_house = None
                    for house in range(1, 7):
                        if name_assignment[house] == 'Eric':
                            eric_house = house
                    if eric_house is None or eric_house >= 4:
                        continue
                    
                    rows = []
                    for house in range(1, 7):
                        rows.append([
                            str(house),
                            name_assignment[house],
                            height_assignment[house],
                            phone_assignment[house]
                        ])
                    
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Height", "PhoneModel"],
                            "rows": rows
                        }
                    }
                    print(json.dumps(solution, indent=2))
                    return
                    
    print('{"solution": {}}')

if __name__ == "__main__":
    main()