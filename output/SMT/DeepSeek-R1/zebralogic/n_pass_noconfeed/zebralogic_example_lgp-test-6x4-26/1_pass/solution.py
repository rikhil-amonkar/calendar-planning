import json
from z3 import *

def main():
    # Initialize solver
    solver = Solver()
    
    # Houses are 1 to 6, but we use 0-indexed arrays of size 6
    houses = [0, 1, 2, 3, 4, 5]
    n = 6
    
    # Attribute value mappings
    name_to_num = {
        'Peter': 1,
        'Bob': 2,
        'Carol': 3,
        'Eric': 4,
        'Alice': 5,
        'Arnold': 6
    }
    num_to_name = {v: k for k, v in name_to_num.items()}
    
    pet_to_num = {
        'bird': 1,
        'dog': 2,
        'cat': 3,
        'rabbit': 4,
        'fish': 5,
        'hamster': 6
    }
    num_to_pet = {v: k for k, v in pet_to_num.items()}
    
    style_to_num = {
        'victorian': 1,
        'ranch': 2,
        'modern': 3,
        'mediterranean': 4,
        'colonial': 5,
        'craftsman': 6
    }
    num_to_style = {v: k for k, v in style_to_num.items()}
    
    birthday_to_num = {
        'mar': 1,
        'sept': 2,
        'may': 3,
        'feb': 4,
        'jan': 5,
        'april': 6
    }
    num_to_birthday = {v: k for k, v in birthday_to_num.items()}
    
    # Create arrays for attributes for each house (0-indexed)
    names = [Int(f'name_{i+1}') for i in houses]
    pets = [Int(f'pet_{i+1}') for i in houses]
    styles = [Int(f'style_{i+1}') for i in houses]
    birthdays = [Int(f'birthday_{i+1}') for i in houses]
    
    # Constraint: All attributes are between 1 and 6
    for i in houses:
        solver.add(And(names[i] >= 1, names[i] <= 6))
        solver.add(And(pets[i] >= 1, pets[i] <= 6))
        solver.add(And(styles[i] >= 1, styles[i] <= 6))
        solver.add(And(birthdays[i] >= 1, birthdays[i] <= 6))
    
    # Constraint: All attributes are distinct
    solver.add(Distinct(names))
    solver.add(Distinct(pets))
    solver.add(Distinct(styles))
    solver.add(Distinct(birthdays))
    
    # Create inverse variables for each attribute value
    inverse_vars = {}
    
    # Names
    for name in name_to_num:
        var = Int(f'{name}_house')
        inverse_vars[f'{name}_house'] = var
        solver.add(Or([And(names[i] == name_to_num[name], var == i+1) for i in houses]))
    
    # Pets
    for pet in pet_to_num:
        var = Int(f'{pet}_house')
        inverse_vars[f'{pet}_house'] = var
        solver.add(Or([And(pets[i] == pet_to_num[pet], var == i+1) for i in houses]))
    
    # Styles
    for style in style_to_num:
        var = Int(f'{style}_house')
        inverse_vars[f'{style}_house'] = var
        solver.add(Or([And(styles[i] == style_to_num[style], var == i+1) for i in houses]))
    
    # Birthdays
    for bd in birthday_to_num:
        var = Int(f'{bd}_house')
        inverse_vars[f'{bd}_house'] = var
        solver.add(Or([And(birthdays[i] == birthday_to_num[bd], var == i+1) for i in houses]))
    
    # Add clues
    # 1. Hamster right of March birthday
    solver.add(inverse_vars['hamster_house'] > inverse_vars['mar_house'])
    
    # 2. January left of September birthday
    solver.add(inverse_vars['jan_house'] < inverse_vars['sept_house'])
    
    # 3. May birthday in second house
    solver.add(birthdays[1] == birthday_to_num['may'])
    
    # 4. Colonial style in second house
    solver.add(styles[1] == style_to_num['colonial'])
    
    # 5. Carol in third house
    solver.add(names[2] == name_to_num['Carol'])
    
    # 6. Mediterranean not in sixth house
    solver.add(styles[5] != style_to_num['mediterranean'])
    
    # 7. Fish right of Bob
    solver.add(inverse_vars['fish_house'] > inverse_vars['Bob_house'])
    
    # 8. Eric in sixth house
    solver.add(names[5] == name_to_num['Eric'])
    
    # 9. One house between cat and Victorian
    cat_house = inverse_vars['cat_house']
    victorian_house = inverse_vars['victorian_house']
    solver.add(Or(cat_house - victorian_house == 2, victorian_house - cat_house == 2))
    
    # 10. Two houses between Victorian and hamster
    hamster_house = inverse_vars['hamster_house']
    solver.add(Or(victorian_house - hamster_house == 3, hamster_house - victorian_house == 3))
    
    # 11. Craftsman is Arnold
    solver.add(inverse_vars['craftsman_house'] == inverse_vars['Arnold_house'])
    
    # 12. Colonial left of modern
    solver.add(inverse_vars['colonial_house'] < inverse_vars['modern_house'])
    
    # 13. Fish not in second house
    solver.add(inverse_vars['fish_house'] != 2)
    
    # 14. Peter is colonial
    solver.add(inverse_vars['Peter_house'] == inverse_vars['colonial_house'])
    
    # 15. January directly left of April
    solver.add(inverse_vars['jan_house'] + 1 == inverse_vars['april_house'])
    
    # 16. One house between bird and modern
    bird_house = inverse_vars['bird_house']
    modern_house = inverse_vars['modern_house']
    solver.add(Or(bird_house - modern_house == 2, modern_house - bird_house == 2))
    
    # 17. Carol is March birthday
    solver.add(inverse_vars['Carol_house'] == inverse_vars['mar_house'])
    
    # 18. Craftsman in fourth house
    solver.add(inverse_vars['craftsman_house'] == 4)
    
    # 19. Dog in fourth house
    solver.add(inverse_vars['dog_house'] == 4)
    
    # Check and get model
    if solver.check() == sat:
        model = solver.model()
        
        # Build results
        result = []
        for i in houses:
            house_num = i + 1
            name_val = model.eval(names[i]).as_long()
            pet_val = model.eval(pets[i]).as_long()
            style_val = model.eval(styles[i]).as_long()
            birthday_val = model.eval(birthdays[i]).as_long()
            
            name_str = num_to_name[name_val]
            pet_str = num_to_pet[pet_val]
            style_str = num_to_style[style_val]
            birthday_str = num_to_birthday[birthday_val]
            
            result.append([str(house_num), name_str, pet_str, style_str, birthday_str])
        
        # Format output JSON
        output = {
            "solution": {
                "header": ["House", "Name", "Pet", "HouseStyle", "Birthday"],
                "rows": result
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()