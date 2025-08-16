from z3 import *
import json

def main():
    # Define the attribute strings
    name_strs = ['Alice', 'Arnold', 'Carol', 'Peter', 'Bob', 'Eric']
    phone_strs = ['huawei p50', 'iphone 13', 'xiaomi mi 11', 'oneplus 9', 'samsung galaxy s21', 'google pixel 6']
    
    # Create enums for names and phones
    Name, name_consts = EnumSort('Name', [n.replace(' ', '_') for n in name_strs])
    Phone, phone_consts = EnumSort('Phone', [p.replace(' ', '_') for p in phone_strs])
    
    # Create mappings from enum constants to original strings
    name_to_str = {name_consts[i]: name_strs[i] for i in range(len(name_strs))}
    phone_to_str = {phone_consts[i]: phone_strs[i] for i in range(len(phone_strs))}
    
    # Create variables for each house
    names = [Const(f'name_{i+1}', Name) for i in range(6)]
    phones = [Const(f'phone_{i+1}', Phone) for i in range(6)]
    
    s = Solver()
    
    # Distinct constraints
    s.add(Distinct(names))
    s.add(Distinct(phones))
    
    # Fixed assignments from clues
    s.add(names[0] == name_consts[name_strs.index('Eric')])
    s.add(phones[0] == phone_consts[phone_strs.index('huawei p50')])
    s.add(phones[2] == phone_consts[phone_strs.index('xiaomi mi 11')])
    s.add(names[5] == name_consts[name_strs.index('Arnold')])
    s.add(phones[5] == phone_consts[phone_strs.index('oneplus 9')])
    
    # Clue 1: iPhone 13 user is Alice
    alice = name_consts[name_strs.index('Alice')]
    iphone13 = phone_consts[phone_strs.index('iphone 13')]
    for i in range(6):
        s.add((names[i] == alice) == (phones[i] == iphone13))
    
    # Clue 4 and 5: House 2 phone constraints
    google_pixel6 = phone_consts[phone_strs.index('google pixel 6')]
    s.add(phones[1] != google_pixel6)
    s.add(phones[1] != iphone13)
    
    # Clue 6: One house between Bob and Carol
    bob = name_consts[name_strs.index('Bob')]
    carol = name_consts[name_strs.index('Carol')]
    terms = []
    for i in [0, 1, 2, 3]:
        terms.append(And(names[i] == bob, names[i+2] == carol))
        terms.append(And(names[i] == carol, names[i+2] == bob))
    s.add(Or(terms))
    
    # Clue 9: Alice is left of Carol
    terms = []
    for i in range(6):
        for j in range(6):
            if i < j:
                terms.append(And(names[i] == alice, names[j] == carol))
    s.add(Or(terms))
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        rows = []
        for i in range(6):
            house = str(i+1)
            name_val = m.eval(names[i])
            phone_val = m.eval(phones[i])
            name_str = name_to_str[name_val]
            phone_str = phone_to_str[phone_val]
            rows.append([house, name_str, phone_str])
        
        solution = {
            "header": ["House", "Name", "PhoneModel"],
            "rows": rows
        }
        result = {"solution": solution}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()