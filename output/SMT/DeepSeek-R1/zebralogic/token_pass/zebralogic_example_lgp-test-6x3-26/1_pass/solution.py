import json
from z3 import *

def main():
    n = 6
    name_list = ['Alice', 'Eric', 'Bob', 'Peter', 'Arnold', 'Carol']
    height_list = ['very tall', 'tall', 'super tall', 'average', 'very short', 'short']
    phone_list = ['oneplus 9', 'google pixel 6', 'samsung galaxy s21', 'iphone 13', 'huawei p50', 'xiaomi mi 11']
    
    super_tall_index = height_list.index('super tall')
    short_index = height_list.index('short')
    pixel_index = phone_list.index('google pixel 6')
    oneplus_index = phone_list.index('oneplus 9')
    very_short_index = height_list.index('very short')
    very_tall_index = height_list.index('very tall')
    tall_index = height_list.index('tall')
    arnold_index = name_list.index('Arnold')
    carol_index = name_list.index('Carol')
    xiaomi_index = phone_list.index('xiaomi mi 11')
    bob_index = name_list.index('Bob')
    eric_index = name_list.index('Eric')
    peter_index = name_list.index('Peter')
    iphone_index = phone_list.index('iphone 13')
    samsung_index = phone_list.index('samsung galaxy s21')
    
    name_vars = [Int(f"n_{i}") for i in range(n)]
    height_vars = [Int(f"h_{i}") for i in range(n)]
    phone_vars = [Int(f"p_{i}") for i in range(n)]
    
    s = Solver()
    
    for i in range(n):
        s.add(And(name_vars[i] >= 0, name_vars[i] < n))
        s.add(And(height_vars[i] >= 0, height_vars[i] < n))
        s.add(And(phone_vars[i] >= 0, phone_vars[i] < n))
    
    s.add(Distinct(name_vars))
    s.add(Distinct(height_vars))
    s.add(Distinct(phone_vars))
    
    s.add(height_vars[0] == super_tall_index)
    s.add(height_vars[5] == short_index)
    s.add(phone_vars[3] == pixel_index)
    s.add(phone_vars[4] == oneplus_index)
    s.add(height_vars[4] == very_short_index)
    
    for i in range(n):
        s.add(Implies(name_vars[i] == carol_index, And(height_vars[i] == very_tall_index, phone_vars[i] == xiaomi_index)))
    
    for i in range(n):
        s.add(Implies(height_vars[i] == tall_index, name_vars[i] == arnold_index))
    
    s.add(Or([And(name_vars[i] == bob_index, height_vars[i+1] == tall_index) for i in range(0, n-1)]))
    
    s.add(Or([And(phone_vars[j] == iphone_index, Or([name_vars[i] == peter_index for i in range(j)])) for j in range(1, n)]))
    
    s.add(phone_vars[0] != samsung_index)
    
    s.add(Or([name_vars[i] == eric_index for i in range(3)]))
    
    if s.check() == sat:
        model = s.model()
        rows = []
        for i in range(n):
            name_val = model.evaluate(name_vars[i]).as_long()
            height_val = model.evaluate(height_vars[i]).as_long()
            phone_val = model.evaluate(phone_vars[i]).as_long()
            rows.append([str(i+1), name_list[name_val], height_list[height_val], phone_list[phone_val]])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Height", "PhoneModel"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()