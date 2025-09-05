import z3
import json

def main():
    houses = [1, 2, 3, 4, 5]
    
    names = ['Peter', 'Arnold', 'Eric', 'Bob', 'Alice']
    name_dict = {name: idx for idx, name in enumerate(names)}
    
    heights = ['average', 'very tall', 'very short', 'short', 'tall']
    height_dict = {h: idx for idx, h in enumerate(heights)}
    
    cigars = ['prince', 'dunhill', 'blends', 'pall mall', 'blue master']
    cigar_dict = {c: idx for idx, c in enumerate(cigars)}
    
    smoothies = ['lime', 'cherry', 'dragonfruit', 'watermelon', 'desert']
    smoothie_dict = {s: idx for idx, s in enumerate(smoothies)}
    
    phones = ['oneplus 9', 'samsung galaxy s21', 'iphone 13', 'huawei p50', 'google pixel 6']
    phone_dict = {p: idx for idx, p in enumerate(phones)}
    
    n = [z3.Int(f'n_{i}') for i in houses]
    h = [z3.Int(f'h_{i}') for i in houses]
    c = [z3.Int(f'c_{i}') for i in houses]
    s = [z3.Int(f's_{i}') for i in houses]
    p = [z3.Int(f'p_{i}') for i in houses]
    
    solver = z3.Solver()
    
    for i in houses:
        solver.add(z3.And(n[i-1] >= 0, n[i-1] < 5))
        solver.add(z3.And(h[i-1] >= 0, h[i-1] < 5))
        solver.add(z3.And(c[i-1] >= 0, c[i-1] < 5))
        solver.add(z3.And(s[i-1] >= 0, s[i-1] < 5))
        solver.add(z3.And(p[i-1] >= 0, p[i-1] < 5))
    
    solver.add(z3.Distinct(n))
    solver.add(z3.Distinct(h))
    solver.add(z3.Distinct(c))
    solver.add(z3.Distinct(s))
    solver.add(z3.Distinct(p))
    
    # Fixed positions based on logical deduction
    solver.add(n[1] == name_dict['Eric'])  # House 2
    solver.add(n[3] == name_dict['Alice']) # House 4
    solver.add(n[4] == name_dict['Bob'])   # House 5
    
    # 1. The Prince smoker is the Desert smoothie lover.
    for i in houses:
        solver.add(z3.Implies(c[i-1] == cigar_dict['prince'], s[i-1] == smoothie_dict['desert']))
    
    # 2. There is one house between Eric and Alice. (Already handled by fixed positions)
    
    # 3. The person who is short is the person who smokes blends.
    for i in houses:
        solver.add(z3.Implies(h[i-1] == height_dict['short'], c[i-1] == cigar_dict['blends']))
    
    # 4. The person who uses an iPhone 13 is directly left of the person who smokes Blue Master.
    for i in range(0, 4):
        solver.add(z3.Implies(p[i] == phone_dict['iphone 13'], c[i+1] == cigar_dict['blue master']))
    
    # 5. The person who has an average height is the Dunhill smoker.
    for i in houses:
        solver.add(z3.Implies(h[i-1] == height_dict['average'], c[i-1] == cigar_dict['dunhill']))
    
    # 6. Eric is the person who is very tall.
    for i in houses:
        solver.add(z3.Implies(n[i-1] == name_dict['Eric'], h[i-1] == height_dict['very tall']))
    
    # 7. Arnold is directly left of the person who uses a Huawei P50.
    for i in range(0, 4):
        solver.add(z3.Implies(n[i] == name_dict['Arnold'], p[i+1] == phone_dict['huawei p50']))
    
    # 8. Bob is not in the fourth house. (Already handled by fixed positions)
    
    # 9. Eric is directly left of the person who likes Cherry smoothies.
    for i in range(0, 4):
        solver.add(z3.Implies(n[i] == name_dict['Eric'], s[i+1] == smoothie_dict['cherry']))
    
    # 10. Bob is the Dunhill smoker.
    for i in houses:
        solver.add(z3.Implies(n[i-1] == name_dict['Bob'], c[i-1] == cigar_dict['dunhill']))
    
    # 11. The Dragonfruit smoothie lover is Bob.
    for i in houses:
        solver.add(z3.Implies(s[i-1] == smoothie_dict['dragonfruit'], n[i-1] == name_dict['Bob']))
    
    # 12. The person who uses an iPhone 13 and the person who uses a OnePlus 9 are next to each other.
    for i in range(0, 4):
        solver.add(z3.Or(
            z3.And(p[i] == phone_dict['iphone 13'], p[i+1] == phone_dict['oneplus 9']),
            z3.And(p[i] == phone_dict['oneplus 9'], p[i+1] == phone_dict['iphone 13'])
        ))
    
    # 13. The person who uses a Samsung Galaxy S21 is the person who is short.
    for i in houses:
        solver.add(z3.Implies(p[i-1] == phone_dict['samsung galaxy s21'], h[i-1] == height_dict['short']))
    
    # 14. There are two houses between the person who is very tall and the Dragonfruit smoothie lover.
    solver.add(z3.Or(
        z3.And(h[0] == height_dict['very tall'], s[3] == smoothie_dict['dragonfruit']),
        z3.And(h[3] == height_dict['very tall'], s[0] == smoothie_dict['dragonfruit']),
        z3.And(h[1] == height_dict['very tall'], s[4] == smoothie_dict['dragonfruit']),
        z3.And(h[4] == height_dict['very tall'], s[1] == smoothie_dict['dragonfruit'])
    ))
    
    # 15. The person who uses an iPhone 13 is Eric.
    for i in houses:
        solver.add(z3.Implies(p[i-1] == phone_dict['iphone 13'], n[i-1] == name_dict['Eric']))
    
    # 16. The Desert smoothie lover is somewhere to the left of the person who drinks Lime smoothies.
    # Create position variables for desert and lime
    desert_pos = z3.Int('desert_pos')
    lime_pos = z3.Int('lime_pos')
    solver.add(desert_pos >= 1, desert_pos <= 5)
    solver.add(lime_pos >= 1, lime_pos <= 5)
    for i in houses:
        solver.add(z3.Implies(s[i-1] == smoothie_dict['desert'], desert_pos == i))
        solver.add(z3.Implies(s[i-1] == smoothie_dict['lime'], lime_pos == i))
    solver.add(desert_pos < lime_pos)
    
    # 17. Arnold and the person who is very short are next to each other.
    for i in range(0, 4):
        solver.add(z3.Or(
            z3.And(n[i] == name_dict['Arnold'], h[i+1] == height_dict['very short']),
            z3.And(n[i+1] == name_dict['Arnold'], h[i] == height_dict['very short'])
        ))
    
    if solver.check() == z3.sat:
        model = solver.model()
        
        rev_name = {v: k for k, v in name_dict.items()}
        rev_height = {v: k for k, v in height_dict.items()}
        rev_cigar = {v: k for k, v in cigar_dict.items()}
        rev_smoothie = {v: k for k, v in smoothie_dict.items()}
        rev_phone = {v: k for k, v in phone_dict.items()}
        
        rows = []
        for i in houses:
            house_num = str(i)
            name_val = rev_name[model.evaluate(n[i-1]).as_long()]
            height_val = rev_height[model.evaluate(h[i-1]).as_long()]
            cigar_val = rev_cigar[model.evaluate(c[i-1]).as_long()]
            smoothie_val = rev_smoothie[model.evaluate(s[i-1]).as_long()]
            phone_val = rev_phone[model.evaluate(p[i-1]).as_long()]
            rows.append([house_num, name_val, height_val, cigar_val, smoothie_val, phone_val])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Height", "Cigar", "Smoothie", "PhoneModel"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()