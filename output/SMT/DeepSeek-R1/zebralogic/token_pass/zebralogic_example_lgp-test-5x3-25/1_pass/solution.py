from z3 import *

def main():
    s = Solver()
    
    names = ['Arnold', 'Bob', 'Alice', 'Eric', 'Peter']
    heights = ['very_tall', 'average', 'tall', 'very_short', 'short']
    foods = ['stew', 'grilled_cheese', 'spaghetti', 'pizza', 'stir_fry']
    
    name_house = {n: Int(f'{n}_house') for n in names}
    height_house = {h: Int(f'{h}_house') for h in heights}
    food_house = {f: Int(f'{f}_house') for f in foods}
    
    for var in list(name_house.values()) + list(height_house.values()) + list(food_house.values()):
        s.add(var >= 1, var <= 5)
    
    s.add(Distinct(list(name_house.values())))
    s.add(Distinct(list(height_house.values())))
    s.add(Distinct(list(food_house.values())))
    
    s.add(name_house['Alice'] == height_house['short'])
    s.add(height_house['tall'] == 3)
    s.add(height_house['average'] != 2)
    s.add(height_house['average'] < food_house['stew'])
    s.add(food_house['stir_fry'] == name_house['Arnold'])
    s.add(food_house['pizza'] == height_house['tall'])
    s.add(name_house['Eric'] == height_house['tall'])
    s.add(name_house['Arnold'] < name_house['Bob'])
    s.add(name_house['Eric'] < food_house['grilled_cheese'])
    s.add(height_house['very_short'] < name_house['Arnold'])
    
    if s.check() == sat:
        m = s.model()
        
        name_map = {}
        for n, var in name_house.items():
            name_map[m[var].as_long()] = n
        
        height_map = {}
        for h, var in height_house.items():
            height_map[m[var].as_long()] = h
        
        food_map = {}
        for f, var in food_house.items():
            food_map[m[var].as_long()] = f
        
        height_display = {
            'very_tall': 'very tall',
            'average': 'average',
            'tall': 'tall',
            'very_short': 'very short',
            'short': 'short'
        }
        
        food_display = {
            'stew': 'stew',
            'grilled_cheese': 'grilled cheese',
            'spaghetti': 'spaghetti',
            'pizza': 'pizza',
            'stir_fry': 'stir fry'
        }
        
        rows = []
        for i in range(1, 6):
            name_val = name_map[i]
            height_val = height_display[height_map[i]]
            food_val = food_display[food_map[i]]
            rows.append([str(i), name_val, height_val, food_val])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Height", "Food"],
                "rows": rows
            }
        }
        
        import json
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()