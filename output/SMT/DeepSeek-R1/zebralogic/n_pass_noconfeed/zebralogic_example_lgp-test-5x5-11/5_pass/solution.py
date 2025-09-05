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
    
    # Constraints
    # 1. The Prince smoker is the Desert smoothie lover.
    for i in houses:
        solver.add(z3.Implies(c[i-1] == cigar_dict['prince'], s[i-1] == smoothie_dict['desert']))
    
    # 2. There is one house between Eric and Alice.
    eric_index = z3.Int('eric_index')
    alice_index = z3.Int('alice_index')
    solver.add(eric_index >= 1, eric_index <= 5)
    solver.add(alice_index >= 1, alice_index <= 5)
    for i in houses:
        solver.add(z3.Implies(n[i-1] == name_dict['Eric'], eric_index == i))
        solver.add(z3.Implies(n[i-1] == name_dict['Alice'], alice_index == i))
    solver.add(z3.Or(
        eric_index == alice_index - 2,
        eric_index == alice_index + 2
    ))
    
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
    
    # 8. Bob is not in the fourth house.
    for i in houses:
        solver.add(z3.Implies(n[i-1] == name_dict['Bob'], z3.Not(i == 4)))
    
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
    very_tall_pos = z3.Int('very_tall_pos')
    dragonfruit_pos = z3.Int('dragonfruit_pos')
    solver.add(very_tall_pos >= 1, very_tall_pos <= 5)
    solver.add(dragonfruit_pos >= 1, dragonfruit_pos <= 5)
    for i in houses:
        solver.add(z3.Implies(h[i-1] == height_dict['very tall'], very_tall_pos == i))
        solver.add(z3.Implies(s[i-1] == smoothie_dict['dragonfruit'], dragonfruit_pos == i))
    solver.add(z3.Or(
        very_tall_pos == dragonfruit_pos - 3,
        very_tall_pos == dragonfruit_pos + 3
    ))
    
    # 15. The person who uses an iPhone 13 is Eric.
    for i in houses:
        solver.add(z3.Implies(p[i-1] == phone_dict['iphone 13'], n[i-1] == name_dict['Eric']))
    
    # 16. The Desert smoothie lover is somewhere to the left of the person who drinks Lime smoothies.
    desert_pos = z3.Int('desert_pos')
    lime_pos = z3.Int('lime_pos')
    solver.add(desert_pos >= 1, desert_pos <= 5)
    solver.add(lime_pos >= 1, lime_pos <= 5)
    for i in houses:
        solver.add(z3.Implies(s[i-1] == smoothie_dict['desert'], desert_pos == i))
        solver.add(z3.Implies(s[i-1] == smoothie_dict['lime'], lime_pos == i))
    solver.add(desert_pos < lime_pos)
    
    # 17. Arnold and the person who is very short are next to each other.
    arnold_pos = z3.Int('arnold_pos')
    very_short_pos = z3.Int('very_short_pos')
    solver.add(arnold_pos >= 1, arnold_pos <= 5)
    solver.add(very_short_pos >= 1, very_short_pos <= 5)
    for i in houses:
        solver.add(z3.Implies(n[i-1] == name_dict['Arnold'], arnold_pos == i))
        solver.add(z3.Implies(h[i-1] == height_dict['very short'], very_short_pos == i))
    solver.add(z3.Or(
        arnold_pos == very_short_pos - 1,
        arnold_pos == very_short_pos + 1
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