import json
from z3 import *

def main():
    # Create solver
    s = Solver()
    
    # Number of houses
    n = 6
    
    # Define attributes
    names = ['Peter', 'Carol', 'Eric', 'Alice', 'Bob', 'Arnold']
    phones = ['huawei p50', 'google pixel 6', 'xiaomi mi 11', 'iphone 13', 'samsung galaxy s21', 'oneplus 9']
    cigars = ['dunhill', 'pall mall', 'blends', 'blue master', 'prince', 'yellow monster']
    flowers = ['daffodils', 'carnations', 'roses', 'tulips', 'lilies', 'iris']
    colors = ['yellow', 'red', 'green', 'blue', 'white', 'purple']
    sports = ['soccer', 'tennis', 'basketball', 'volleyball', 'swimming', 'baseball']
    
    # Create variables for each attribute per house
    name_vars = [Int(f'name_{i}') for i in range(1, n+1)]
    phone_vars = [Int(f'phone_{i}') for i in range(1, n+1)]
    cigar_vars = [Int(f'cigar_{i}') for i in range(1, n+1)]
    flower_vars = [Int(f'flower_{i}') for i in range(1, n+1)]
    color_vars = [Int(f'color_{i}') for i in range(1, n+1)]
    sport_vars = [Int(f'sport_{i}') for i in range(1, n+1)]
    
    # Constraint: All attributes are within valid range (0-5)
    for i in range(n):
        s.add(And(name_vars[i] >= 0, name_vars[i] < n))
        s.add(And(phone_vars[i] >= 0, phone_vars[i] < n))
        s.add(And(cigar_vars[i] >= 0, cigar_vars[i] < n))
        s.add(And(flower_vars[i] >= 0, flower_vars[i] < n))
        s.add(And(color_vars[i] >= 0, color_vars[i] < n))
        s.add(And(sport_vars[i] >= 0, sport_vars[i] < n))
    
    # Constraint: All attributes are distinct within their category
    s.add(Distinct(name_vars))
    s.add(Distinct(phone_vars))
    s.add(Distinct(cigar_vars))
    s.add(Distinct(flower_vars))
    s.add(Distinct(color_vars))
    s.add(Distinct(sport_vars))
    
    # Helper functions
    def find_index(lst, item):
        return lst.index(item)
    
    def left_of(a, a_idx, b, b_idx):
        return Or([And(a[i] == a_idx, b[i+1] == b_idx) for i in range(n-1)])
    
    def right_of(a, a_idx, b, b_idx):
        return left_of(b, b_idx, a, a_idx)
    
    def somewhere_left(a, a_idx, b, b_idx):
        return Or([And(a[i] == a_idx, b[j] == b_idx) for i in range(n) for j in range(i+1, n)])
    
    def somewhere_right(a, a_idx, b, b_idx):
        return somewhere_left(b, b_idx, a, a_idx)
    
    def next_to(a, a_idx, b, b_idx):
        return Or(left_of(a, a_idx, b, b_idx), right_of(a, a_idx, b, b_idx))
    
    def two_between(a, a_idx, b, b_idx):
        # Fixed: Create a single list of all possible conditions
        conditions = []
        for i in range(n-3):
            conditions.append(And(a[i] == a_idx, b[i+3] == b_idx))
            conditions.append(And(a[i+3] == a_idx, b[i] == b_idx))
        return Or(conditions)
    
    # Apply clues
    # 1. The person who uses a OnePlus 9 is in the second house.
    s.add(phone_vars[1] == find_index(phones, 'oneplus 9'))
    
    # 2. The person who uses a Xiaomi Mi 11 is somewhere to the left of the person who uses a Huawei P50.
    s.add(somewhere_left(phone_vars, find_index(phones, 'xiaomi mi 11'), phone_vars, find_index(phones, 'huawei p50')))
    
    # 3. Carol is the person who loves a carnations arrangement.
    carol_idx = find_index(names, 'Carol')
    carnations_idx = find_index(flowers, 'carnations')
    s.add(Or([And(name_vars[i] == carol_idx, flower_vars[i] == carnations_idx) for i in range(n)]))
    
    # 4. The person who loves purple is directly left of the person partial to Pall Mall.
    purple_idx = find_index(colors, 'purple')
    pall_mall_idx = find_index(cigars, 'pall mall')
    s.add(left_of(color_vars, purple_idx, cigar_vars, pall_mall_idx))
    
    # 5. The person whose favorite color is green is the person who smokes Blue Master.
    green_idx = find_index(colors, 'green')
    blue_master_idx = find_index(cigars, 'blue master')
    s.add(Or([And(color_vars[i] == green_idx, cigar_vars[i] == blue_master_idx) for i in range(n)]))
    
    # 6. The person who loves yellow and the person who loves blue are next to each other.
    yellow_idx = find_index(colors, 'yellow')
    blue_idx = find_index(colors, 'blue')
    s.add(next_to(color_vars, yellow_idx, color_vars, blue_idx))
    
    # 7. Eric is somewhere to the right of the person who uses a Samsung Galaxy S21.
    eric_idx = find_index(names, 'Eric')
    samsung_idx = find_index(phones, 'samsung galaxy s21')
    s.add(somewhere_right(name_vars, eric_idx, phone_vars, samsung_idx))
    
    # 8. There are two houses between Carol and the person who loves a bouquet of daffodils.
    carol_idx = find_index(names, 'Carol')
    daffodils_idx = find_index(flowers, 'daffodils')
    s.add(two_between(name_vars, carol_idx, flower_vars, daffodils_idx))
    
    # 9. The Prince smoker is the person who loves basketball.
    prince_idx = find_index(cigars, 'prince')
    basketball_idx = find_index(sports, 'basketball')
    s.add(Or([And(cigar_vars[i] == prince_idx, sport_vars[i] == basketball_idx) for i in range(n)]))
    
    # 10. The Dunhill smoker is the person who loves volleyball.
    dunhill_idx = find_index(cigars, 'dunhill')
    volleyball_idx = find_index(sports, 'volleyball')
    s.add(Or([And(cigar_vars[i] == dunhill_idx, sport_vars[i] == volleyball_idx) for i in range(n)]))
    
    # 11. The person who loves swimming is the person who uses a Google Pixel 6.
    swimming_idx = find_index(sports, 'swimming')
    pixel_idx = find_index(phones, 'google pixel 6')
    s.add(Or([And(sport_vars[i] == swimming_idx, phone_vars[i] == pixel_idx) for i in range(n)]))
    
    # 12. The person who uses a Huawei P50 is directly left of the person who loves white.
    huawei_idx = find_index(phones, 'huawei p50')
    white_idx = find_index(colors, 'white')
    s.add(left_of(phone_vars, huawei_idx, color_vars, white_idx))
    
    # 13. The person who uses a OnePlus 9 and the person who loves the rose bouquet are next to each other.
    oneplus_idx = find_index(phones, 'oneplus 9')
    roses_idx = find_index(flowers, 'roses')
    s.add(next_to(phone_vars, oneplus_idx, flower_vars, roses_idx))
    
    # 14. The person who loves the bouquet of iris is somewhere to the left of Eric.
    iris_idx = find_index(flowers, 'iris')
    eric_idx = find_index(names, 'Eric')
    s.add(somewhere_left(flower_vars, iris_idx, name_vars, eric_idx))
    
    # 15. The Dunhill smoker is Peter.
    dunhill_idx = find_index(cigars, 'dunhill')
    peter_idx = find_index(names, 'Peter')
    s.add(Or([And(cigar_vars[i] == dunhill_idx, name_vars[i] == peter_idx) for i in range(n)]))
    
    # 16. The person who loves blue is Peter.
    blue_idx = find_index(colors, 'blue')
    peter_idx = find_index(names, 'Peter')
    s.add(Or([And(color_vars[i] == blue_idx, name_vars[i] == peter_idx) for i in range(n)]))
    
    # 17. The person who loves the vase of tulips is Bob.
    tulips_idx = find_index(flowers, 'tulips')
    bob_idx = find_index(names, 'Bob')
    s.add(Or([And(flower_vars[i] == tulips_idx, name_vars[i] == bob_idx) for i in range(n)]))
    
    # 18. Alice is in the first house.
    alice_idx = find_index(names, 'Alice')
    s.add(name_vars[0] == alice_idx)
    
    # 19. The person who loves baseball is directly left of the person who smokes Blue Master.
    baseball_idx = find_index(sports, 'baseball')
    blue_master_idx = find_index(cigars, 'blue master')
    s.add(left_of(sport_vars, baseball_idx, cigar_vars, blue_master_idx))
    
    # 20. The person who uses a Google Pixel 6 is somewhere to the right of the person who smokes many unique blends.
    pixel_idx = find_index(phones, 'google pixel 6')
    blends_idx = find_index(cigars, 'blends')
    s.add(somewhere_right(phone_vars, pixel_idx, cigar_vars, blends_idx))
    
    # 21. The person who loves soccer is Carol.
    soccer_idx = find_index(sports, 'soccer')
    carol_idx = find_index(names, 'Carol')
    s.add(Or([And(sport_vars[i] == soccer_idx, name_vars[i] == carol_idx) for i in range(n)]))
    
    # 22. The person who loves a carnations arrangement is directly left of the person who smokes many unique blends.
    carnations_idx = find_index(flowers, 'carnations')
    blends_idx = find_index(cigars, 'blends')
    s.add(left_of(flower_vars, carnations_idx, cigar_vars, blends_idx))
    
    # 23. Eric is the person who smokes many unique blends.
    eric_idx = find_index(names, 'Eric')
    blends_idx = find_index(cigars, 'blends')
    s.add(Or([And(name_vars[i] == eric_idx, cigar_vars[i] == blends_idx) for i in range(n)]))
    
    # 24. The person who loves volleyball is the person who uses an iPhone 13.
    volleyball_idx = find_index(sports, 'volleyball')
    iphone_idx = find_index(phones, 'iphone 13')
    s.add(Or([And(sport_vars[i] == volleyball_idx, phone_vars[i] == iphone_idx) for i in range(n)]))
    
    # Check if satisfiable
    if s.check() == sat:
        model = s.model()
        
        # Extract solution
        solution = []
        for i in range(n):
            house_data = [str(i+1)]
            
            # Get name
            name_val = model.eval(name_vars[i]).as_long()
            house_data.append(names[name_val])
            
            # Get phone
            phone_val = model.eval(phone_vars[i]).as_long()
            house_data.append(phones[phone_val])
            
            # Get cigar
            cigar_val = model.eval(cigar_vars[i]).as_long()
            house_data.append(cigars[cigar_val])
            
            # Get flower
            flower_val = model.eval(flower_vars[i]).as_long()
            house_data.append(flowers[flower_val])
            
            # Get color
            color_val = model.eval(color_vars[i]).as_long()
            house_data.append(colors[color_val])
            
            # Get sport
            sport_val = model.eval(sport_vars[i]).as_long()
            house_data.append(sports[sport_val])
            
            solution.append(house_data)
        
        # Create output JSON
        output = {
            "solution": {
                "header": ["House", "Name", "PhoneModel", "Cigar", "Flower", "Color", "FavoriteSport"],
                "rows": solution
            }
        }
        
        print(json.dumps(output, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()