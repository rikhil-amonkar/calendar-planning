from z3 import *
import json

def main():
    # Define the enums for each attribute
    Name, (Carol, Bob, Alice, Arnold, Eric, Peter) = EnumSort('Name', ['Carol', 'Bob', 'Alice', 'Arnold', 'Eric', 'Peter'])
    Phone, (samsung_galaxy_s21, google_pixel_6, iphone_13, huawei_p50, oneplus_9, xiaomi_mi_11) = EnumSort('Phone', [
        'samsung_galaxy_s21', 'google_pixel_6', 'iphone_13', 'huawei_p50', 'oneplus_9', 'xiaomi_mi_11'])
    Nationality, (swede, chinese, norwegian, dane, german, brit) = EnumSort('Nationality', ['swede', 'chinese', 'norwegian', 'dane', 'german', 'brit'])
    Color, (blue, red, yellow, green, white, purple) = EnumSort('Color', ['blue', 'red', 'yellow', 'green', 'white', 'purple'])
    
    # Create variables for each house (0-indexed for houses 1-6)
    n = [Const(f'n{i}', Name) for i in range(6)]
    p = [Const(f'p{i}', Phone) for i in range(6)]
    nat = [Const(f'nat{i}', Nationality) for i in range(6)]
    c = [Const(f'c{i}', Color) for i in range(6)]
    
    s = Solver()
    
    # All attributes are distinct
    s.add(Distinct(n))
    s.add(Distinct(p))
    s.add(Distinct(nat))
    s.add(Distinct(c))
    
    # Clue 1: Carol is not in the third house
    s.add(n[2] != Carol)
    
    # Clue 2: One house between Dane and British
    for i in range(4):
        s.add(Or(
            And(nat[i] == dane, nat[i+2] == brit),
            And(nat[i] == brit, nat[i+2] == dane)
        ))
    
    # Clue 3: Carol loves green
    for i in range(6):
        s.add(Implies(n[i] == Carol, c[i] == green))
    
    # Clue 4: Arnold directly left of Alice
    for i in range(5):
        s.add(Or(And(n[i] == Arnold, n[i+1] == Alice)))
    
    # Clue 5: Alice is German
    for i in range(6):
        s.add(Implies(n[i] == Alice, nat[i] == german))
    
    # Clue 6: OnePlus 9 user loves purple
    for i in range(6):
        s.add(Implies(p[i] == oneplus_9, c[i] == purple))
    
    # Clue 7: Huawei P50 not in third house
    s.add(p[2] != huawei_p50)
    
    # Clue 8: Samsung Galaxy S21 in fifth house
    s.add(p[4] == samsung_galaxy_s21)
    
    # Clue 9: White right of red
    red_index = Int('red_index')
    white_index = Int('white_index')
    s.add(red_index >= 0, red_index < 6)
    s.add(white_index >= 0, white_index < 6)
    s.add(ForAll([red_index, white_index], Implies(And(c[red_index] == red, c[white_index] == white), white_index > red_index)))
    
    # Clue 10: Samsung user is Bob
    for i in range(6):
        s.add(Implies(p[i] == samsung_galaxy_s21, n[i] == Bob))
    
    # Clue 11: Dane loves yellow
    for i in range(6):
        s.add(Implies(nat[i] == dane, c[i] == yellow))
    
    # Clue 12: Samsung left of Peter
    samsung_house = Int('samsung_house')
    peter_house = Int('peter_house')
    s.add(samsung_house >= 0, samsung_house < 6)
    s.add(peter_house >= 0, peter_house < 6)
    s.add(ForAll([samsung_house, peter_house], Implies(And(p[samsung_house] == samsung_galaxy_s21, n[peter_house] == Peter), samsung_house < peter_house)))
    
    # Clue 13: Blue lover is Peter
    for i in range(6):
        s.add(Implies(c[i] == blue, n[i] == Peter))
    
    # Clue 14: Peter is British
    for i in range(6):
        s.add(Implies(n[i] == Peter, nat[i] == brit))
    
    # Clue 15: Samsung directly left of iPhone 13
    s.add(p[5] == iphone_13)  # Since Samsung is in house 5 (index 4)
    
    # Clue 16: Norwegian loves purple
    for i in range(6):
        s.add(Implies(nat[i] == norwegian, c[i] == purple))
    
    # Clue 17: Xiaomi Mi 11 user is Chinese
    for i in range(6):
        s.add(Implies(p[i] == xiaomi_mi_11, nat[i] == chinese))
    
    # Check and get solution
    if s.check() == sat:
        m = s.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "PhoneModel", "Nationality", "Color"],
                "rows": []
            }
        }
        for i in range(6):
            house_num = str(i+1)
            name_val = m.evaluate(n[i])
            phone_val = m.evaluate(p[i])
            nat_val = m.evaluate(nat[i])
            color_val = m.evaluate(c[i])
            
            name_str = str(name_val)
            phone_str = str(phone_val).replace('_', ' ')
            nat_str = str(nat_val)
            color_str = str(color_val)
            
            solution["solution"]["rows"].append([house_num, name_str, phone_str, nat_str, color_str])
        
        print(json.dumps(solution, indent=2))
    else:
        print('{"solution": {"header": [], "rows": []}}')

if __name__ == "__main__":
    main()