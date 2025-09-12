import json
from z3 import *

def main():
    # Create solver
    s = Solver()
    
    # Define attributes with integer mappings
    names = ['Peter', 'Arnold', 'Eric', 'Bob', 'Alice']
    name_to_int = {name: i+1 for i, name in enumerate(names)}
    
    heights = ['average', 'very tall', 'very short', 'short', 'tall']
    height_to_int = {height: i+1 for i, height in enumerate(heights)}
    
    cigars = ['prince', 'dunhill', 'blends', 'pall mall', 'blue master']
    cigar_to_int = {cigar: i+1 for i, cigar in enumerate(cigars)}
    
    smoothies = ['lime', 'cherry', 'dragonfruit', 'watermelon', 'desert']
    smoothie_to_int = {smoothie: i+1 for i, smoothie in enumerate(smoothies)}
    
    phones = ['oneplus 9', 'samsung galaxy s21', 'iphone 13', 'huawei p50', 'google pixel 6']
    phone_to_int = {phone: i+1 for i, phone in enumerate(phones)}
    
    # Create variables for each house and attribute
    house_count = 5
    name_vars = [Int(f'name_{i}') for i in range(1, house_count+1)]
    height_vars = [Int(f'height_{i}') for i in range(1, house_count+1)]
    cigar_vars = [Int(f'cigar_{i}') for i in range(1, house_count+1)]
    smoothie_vars = [Int(f'smoothie_{i}') for i in range(1, house_count+1)]
    phone_vars = [Int(f'phone_{i}') for i in range(1, house_count+1)]
    
    # Add constraints for each variable to be in valid range
    for var in name_vars + height_vars + cigar_vars + smoothie_vars + phone_vars:
        s.add(var >= 1, var <= house_count)
    
    # Add distinct constraints for each attribute category
    s.add(Distinct(name_vars))
    s.add(Distinct(height_vars))
    s.add(Distinct(cigar_vars))
    s.add(Distinct(smoothie_vars))
    s.add(Distinct(phone_vars))
    
    # Clue 1: The Prince smoker is the Desert smoothie lover.
    s.add(Exists([i], And(i >= 1, i <= house_count, 
                         cigar_vars[i-1] == cigar_to_int['prince'],
                         smoothie_vars[i-1] == smoothie_to_int['desert'])))
    
    # Clue 2: There is one house between Eric and Alice.
    eric_house = Int('eric_house')
    alice_house = Int('alice_house')
    s.add(eric_house >= 1, eric_house <= house_count)
    s.add(alice_house >= 1, alice_house <= house_count)
    s.add(Exists([i], And(i >= 1, i <= house_count, name_vars[i-1] == name_to_int['Eric'])))
    s.add(Exists([i], And(i >= 1, i <= house_count, name_vars[i-1] == name_to_int['Alice'])))
    s.add(Abs(eric_house - alice_house) == 2)
    
    # Clue 3: The person who is short is the person who smokes blends.
    s.add(Exists([i], And(i >= 1, i <= house_count,
                         height_vars[i-1] == height_to_int['short'],
                         cigar_vars[i-1] == cigar_to_int['blends'])))
    
    # Clue 4: iPhone 13 user is directly left of Blue Master smoker.
    s.add(Exists([i], And(i >= 1, i < house_count,
                         phone_vars[i-1] == phone_to_int['iphone 13'],
                         cigar_vars[i] == cigar_to_int['blue master'])))
    
    # Clue 5: Average height is Dunhill smoker.
    s.add(Exists([i], And(i >= 1, i <= house_count,
                         height_vars[i-1] == height_to_int['average'],
                         cigar_vars[i-1] == cigar_to_int['dunhill'])))
    
    # Clue 6: Eric is very tall.
    s.add(Exists([i], And(i >= 1, i <= house_count,
                         name_vars[i-1] == name_to_int['Eric'],
                         height_vars[i-1] == height_to_int['very tall'])))
    
    # Clue 7: Arnold is directly left of Huawei P50 user.
    s.add(Exists([i], And(i >= 1, i < house_count,
                         name_vars[i-1] == name_to_int['Arnold'],
                         phone_vars[i] == phone_to_int['huawei p50'])))
    
    # Clue 8: Bob is not in fourth house.
    s.add(name_vars[3] != name_to_int['Bob'])
    
    # Clue 9: Eric is directly left of Cherry smoothie lover.
    s.add(Exists([i], And(i >= 1, i < house_count,
                         name_vars[i-1] == name_to_int['Eric'],
                         smoothie_vars[i] == smoothie_to_int['cherry'])))
    
    # Clue 10: Bob is Dunhill smoker.
    s.add(Exists([i], And(i >= 1, i <= house_count,
                         name_vars[i-1] == name_to_int['Bob'],
                         cigar_vars[i-1] == cigar_to_int['dunhill'])))
    
    # Clue 11: Dragonfruit smoothie lover is Bob.
    s.add(Exists([i], And(i >= 1, i <= house_count,
                         smoothie_vars[i-1] == smoothie_to_int['dragonfruit'],
                         name_vars[i-1] == name_to_int['Bob'])))
    
    # Clue 12: iPhone 13 and OnePlus 9 users are adjacent.
    s.add(Exists([i, j], And(i >= 1, i <= house_count, j >= 1, j <= house_count,
                            phone_vars[i-1] == phone_to_int['iphone 13'],
                            phone_vars[j-1] == phone_to_int['oneplus 9'],
                            Abs(i - j) == 1)))
    
    # Clue 13: Samsung Galaxy S21 user is short.
    s.add(Exists([i], And(i >= 1, i <= house_count,
                         phone_vars[i-1] == phone_to_int['samsung galaxy s21'],
                         height_vars[i-1] == height_to_int['short'])))
    
    # Clue 14: Two houses between very tall and Dragonfruit smoothie lover.
    s.add(Exists([i, j], And(i >= 1, i <= house_count, j >= 1, j <= house_count,
                            height_vars[i-1] == height_to_int['very tall'],
                            smoothie_vars[j-1] == smoothie_to_int['dragonfruit'],
                            Abs(i - j) == 3)))
    
    # Clue 15: iPhone 13 user is Eric.
    s.add(Exists([i], And(i >= 1, i <= house_count,
                         phone_vars[i-1] == phone_to_int['iphone 13'],
                         name_vars[i-1] == name_to_int['Eric'])))
    
    # Clue 16: Desert smoothie left of Lime smoothie.
    s.add(Exists([i, j], And(i >= 1, i <= house_count, j >= 1, j <= house_count,
                            smoothie_vars[i-1] == smoothie_to_int['desert'],
                            smoothie_vars[j-1] == smoothie_to_int['lime'],
                            i < j)))
    
    # Clue 17: Arnold and very short are adjacent.
    s.add(Exists([i, j], And(i >= 1, i <= house_count, j >= 1, j <= house_count,
                            name_vars[i-1] == name_to_int['Arnold'],
                            height_vars[j-1] == height_to_int['very short'],
                            Abs(i - j) == 1)))
    
    # Check satisfiability
    if s.check() == sat:
        m = s.model()
        
        # Create reverse mappings for decoding
        int_to_name = {v: k for k, v in name_to_int.items()}
        int_to_height = {v: k for k, v in height_to_int.items()}
        int_to_cigar = {v: k for k, v in cigar_to_int.items()}
        int_to_smoothie = {v: k for k, v in smoothie_to_int.items()}
        int_to_phone = {v: k for k, v in phone_to_int.items()}
        
        # Collect results
        result = []
        for i in range(house_count):
            house_num = str(i+1)
            name_val = int_to_name[m.evaluate(name_vars[i]).as_long()]
            height_val = int_to_height[m.evaluate(height_vars[i]).as_long()]
            cigar_val = int_to_cigar[m.evaluate(cigar_vars[i]).as_long()]
            smoothie_val = int_to_smoothie[m.evaluate(smoothie_vars[i]).as_long()]
            phone_val = int_to_phone[m.evaluate(phone_vars[i]).as_long()]
            result.append([house_num, name_val, height_val, cigar_val, smoothie_val, phone_val])
        
        # Format output JSON
        solution = {
            "solution": {
                "header": ["House", "Name", "Height", "Cigar", "Smoothie", "PhoneModel"],
                "rows": result
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()