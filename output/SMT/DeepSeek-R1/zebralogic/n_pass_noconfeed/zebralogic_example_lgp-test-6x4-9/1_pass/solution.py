import json
from z3 import *

def main():
    solver = Solver()
    
    # Define enums for each category with exact strings
    NameSort, (Carol, Bob, Alice, Arnold, Eric, Peter) = EnumSort('Name', 
        ['Carol', 'Bob', 'Alice', 'Arnold', 'Eric', 'Peter'])
    PhoneSort, (samsung_galaxy_s21, google_pixel_6, iphone_13, huawei_p50, oneplus_9, xiaomi_mi_11) = EnumSort('PhoneModel', 
        ['samsung galaxy s21', 'google pixel 6', 'iphone 13', 'huawei p50', 'oneplus 9', 'xiaomi mi 11'])
    NationalitySort, (swede, chinese, norwegian, dane, german, brit) = EnumSort('Nationality', 
        ['swede', 'chinese', 'norwegian', 'dane', 'german', 'brit'])
    ColorSort, (blue, red, yellow, green, white, purple) = EnumSort('Color', 
        ['blue', 'red', 'yellow', 'green', 'white', 'purple'])
    
    # Create variables for each house (0-indexed representing houses 1-6)
    names = [Const(f'name_{i}', NameSort) for i in range(6)]
    phones = [Const(f'phone_{i}', PhoneSort) for i in range(6)]
    nationalities = [Const(f'nationality_{i}', NationalitySort) for i in range(6)]
    colors = [Const(f'color_{i}', ColorSort) for i in range(6)]
    
    # Each attribute must be distinct per house
    solver.add(Distinct(names))
    solver.add(Distinct(phones))
    solver.add(Distinct(nationalities))
    solver.add(Distinct(colors))
    
    # Add constraints from clues
    # 1. Carol is not in the third house
    solver.add(names[2] != Carol)
    
    # 2. One house between Dane and British
    dane_index = Const('dane_index', IntSort())
    brit_index = Const('brit_index', IntSort())
    solver.add(Or(
        dane_index == brit_index + 2,
        dane_index == brit_index - 2
    ))
    for i in range(6):
        solver.add(Implies(nationalities[i] == dane, dane_index == i))
        solver.add(Implies(nationalities[i] == brit, brit_index == i))
    
    # 3. Carol loves green
    for i in range(6):
        solver.add(Implies(names[i] == Carol, colors[i] == green))
    
    # 4. Arnold directly left of Alice
    for i in range(5):
        solver.add(Implies(names[i] == Arnold, names[i+1] == Alice))
    solver.add(Not(Or([names[i] == Arnold for i in [5]])))  # Arnold cannot be in last house
    
    # 5. Alice is German
    for i in range(6):
        solver.add(Implies(names[i] == Alice, nationalities[i] == german))
    
    # 6. OnePlus 9 user loves purple
    for i in range(6):
        solver.add(Implies(phones[i] == oneplus_9, colors[i] == purple))
    
    # 7. Huawei P50 not in third house
    solver.add(phones[2] != huawei_p50)
    
    # 8. Samsung Galaxy S21 in fifth house
    solver.add(phones[4] == samsung_galaxy_s21)
    
    # 9. White right of red
    white_index = Const('white_index', IntSort())
    red_index = Const('red_index', IntSort())
    solver.add(white_index > red_index)
    for i in range(6):
        solver.add(Implies(colors[i] == white, white_index == i))
        solver.add(Implies(colors[i] == red, red_index == i))
    
    # 10. Samsung user is Bob
    for i in range(6):
        solver.add(Implies(phones[i] == samsung_galaxy_s21, names[i] == Bob))
    
    # 11. Dane loves yellow
    for i in range(6):
        solver.add(Implies(nationalities[i] == dane, colors[i] == yellow))
    
    # 12. Samsung left of Peter
    samsung_index = Const('samsung_index', IntSort())
    peter_index = Const('peter_index', IntSort())
    solver.add(samsung_index < peter_index)
    for i in range(6):
        solver.add(Implies(phones[i] == samsung_galaxy_s21, samsung_index == i))
        solver.add(Implies(names[i] == Peter, peter_index == i))
    
    # 13. Blue lover is Peter
    for i in range(6):
        solver.add(Implies(colors[i] == blue, names[i] == Peter))
    
    # 14. Peter is British
    for i in range(6):
        solver.add(Implies(names[i] == Peter, nationalities[i] == brit))
    
    # 15. Samsung directly left of iPhone 13
    iphone_index = Const('iphone_index', IntSort())
    solver.add(samsung_index + 1 == iphone_index)
    for i in range(6):
        solver.add(Implies(phones[i] == iphone_13, iphone_index == i))
    
    # 16. Norwegian loves purple
    for i in range(6):
        solver.add(Implies(nationalities[i] == norwegian, colors[i] == purple))
    
    # 17. Xiaomi user is Chinese
    for i in range(6):
        solver.add(Implies(phones[i] == xiaomi_mi_11, nationalities[i] == chinese))
    
    # Check and get model
    if solver.check() == sat:
        model = solver.model()
        
        # Prepare solution data
        header = ["House", "Name", "PhoneModel", "Nationality", "Color"]
        rows = []
        for i in range(6):
            name_val = model.eval(names[i])
            phone_val = model.eval(phones[i])
            nationality_val = model.eval(nationalities[i])
            color_val = model.eval(colors[i])
            rows.append([
                str(i+1),
                str(name_val),
                str(phone_val),
                str(nationality_val),
                str(color_val)
            ])
        
        solution = {
            "solution": {
                "header": header,
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()