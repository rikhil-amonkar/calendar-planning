import itertools
import json

def main():
    names = ['Alice', 'Arnold', 'Carol', 'Peter', 'Bob', 'Eric']
    phones = ['huawei p50', 'iphone 13', 'xiaomi mi 11', 'oneplus 9', 'samsung galaxy s21', 'google pixel 6']
    
    # Generate possible name permutations with Eric in house 1 (index 0) and Arnold in house 6 (index 5)
    remaining_names = ['Alice', 'Carol', 'Peter', 'Bob']
    name_perms = itertools.permutations(remaining_names)
    
    # Generate possible phone permutations with fixed positions
    remaining_phones = ['iphone 13', 'samsung galaxy s21', 'google pixel 6']
    phone_positions = list(itertools.permutations(remaining_phones))
    
    solution_found = None
    
    for name_perm in name_perms:
        current_names = ['Eric'] + list(name_perm) + ['Arnold']
        
        for phone_part in phone_positions:
            # Check constraints for house 2 (index 1) phone
            if phone_part[0] in ['google pixel 6', 'iphone 13']:
                continue
            current_phones = [
                'huawei p50',  # house 1 (index 0)
                phone_part[0],  # house 2 (index 1)
                'xiaomi mi 11',  # house 3 (index 2)
                phone_part[1],  # house 4 (index 3)
                phone_part[2],  # house 5 (index 4)
                'oneplus 9'  # house 6 (index 5)
            ]
            
            # Check clue 1: iPhone 13 user is Alice
            try:
                iphone13_idx = current_phones.index('iphone 13')
            except ValueError:
                # If 'iphone 13' not found, skip (but it should be there)
                continue
            if current_names[iphone13_idx] != 'Alice':
                continue
            
            # Check clue 6: Bob and Carol have one house between them
            bob_idx = current_names.index('Bob')
            carol_idx = current_names.index('Carol')
            if abs(bob_idx - carol_idx) != 2:
                continue
            
            # Check clue 9: Alice is left of Carol
            alice_idx = current_names.index('Alice')
            if alice_idx >= carol_idx:
                continue
            
            # If all constraints are satisfied, build the solution
            rows = []
            for i in range(6):
                house_num = str(i + 1)
                name = current_names[i]
                phone = current_phones[i]
                rows.append([house_num, name, phone])
            
            solution_found = {
                "solution": {
                    "header": ["House", "Name", "PhoneModel"],
                    "rows": rows
                }
            }
            # Return after finding the first solution
            print(json.dumps(solution_found))
            return
    
    # If no solution found (unlikely)
    print(json.dumps({"solution": {"header": [], "rows": []}}))

if __name__ == "__main__":
    main()