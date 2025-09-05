import z3
import json

def main():
    solver = z3.Solver()
    
    # Define the variables for each attribute's house assignment
    names = ['Alice', 'Peter', 'Bob', 'Eric', 'Arnold']
    name_vars = [z3.Int(f'{name}_house') for name in names]
    
    heights = ['very short', 'short', 'tall', 'average', 'very tall']
    height_vars = [z3.Int(f'{height}_house') for height in heights]
    
    mothers = ['Janelle', 'Kailyn', 'Penny', 'Holly', 'Aniya']
    mother_vars = [z3.Int(f'{mother}_house') for mother in mothers]
    
    hair_colors = ['blonde', 'black', 'gray', 'red', 'brown']
    hair_vars = [z3.Int(f'{color}_house') for color in hair_colors]
    
    all_vars = name_vars + height_vars + mother_vars + hair_vars
    
    # Each attribute variable must be between 1 and 5
    for var in all_vars:
        solver.add(z3.And(var >= 1, var <= 5))
    
    # Each set of attributes must have distinct houses
    solver.add(z3.Distinct(name_vars))
    solver.add(z3.Distinct(height_vars))
    solver.add(z3.Distinct(mother_vars))
    solver.add(z3.Distinct(hair_vars))
    
    # Add constraints from clues
    # 1. The person who is tall is The person whose mother's name is Holly.
    tall_index = heights.index('tall')
    holly_index = mothers.index('Holly')
    solver.add(height_vars[tall_index] == mother_vars[holly_index])
    
    # 2. There are two houses between average height and short height.
    average_index = heights.index('average')
    short_index = heights.index('short')
    solver.add(z3.Or(
        height_vars[average_index] == height_vars[short_index] + 3,
        height_vars[average_index] == height_vars[short_index] - 3
    ))
    
    # 3. Gray hair is directly left of Janelle mother.
    gray_index = hair_colors.index('gray')
    janelle_index = mothers.index('Janelle')
    solver.add(hair_vars[gray_index] == mother_vars[janelle_index] - 1)
    
    # 4. Black hair not in fourth house.
    black_index = hair_colors.index('black')
    solver.add(hair_vars[black_index] != 4)
    
    # 5. Eric has black hair.
    eric_index = names.index('Eric')
    solver.add(name_vars[eric_index] == hair_vars[black_index])
    
    # 6. Very short height is Penny mother.
    very_short_index = heights.index('very short')
    penny_index = mothers.index('Penny')
    solver.add(height_vars[very_short_index] == mother_vars[penny_index])
    
    # 7. Eric and gray hair are next to each other.
    solver.add(z3.Or(
        name_vars[eric_index] == hair_vars[gray_index] + 1,
        name_vars[eric_index] == hair_vars[gray_index] - 1
    ))
    
    # 8. Bob in fifth house.
    bob_index = names.index('Bob')
    solver.add(name_vars[bob_index] == 5)
    
    # 9. Red hair is Peter.
    red_index = hair_colors.index('red')
    peter_index = names.index('Peter')
    solver.add(hair_vars[red_index] == name_vars[peter_index])
    
    # 10. Kailyn mother directly left of short height.
    kailyn_index = mothers.index('Kailyn')
    solver.add(mother_vars[kailyn_index] == height_vars[short_index] - 1)
    
    # 11. Arnold has brown hair.
    arnold_index = names.index('Arnold')
    brown_index = hair_colors.index('brown')
    solver.add(name_vars[arnold_index] == hair_vars[brown_index])
    
    # 12. Brown hair left of Janelle mother.
    solver.add(hair_vars[brown_index] < mother_vars[janelle_index])
    
    # 13. Aniya mother and very short height are next to each other.
    aniya_index = mothers.index('Aniya')
    solver.add(z3.Or(
        mother_vars[aniya_index] == height_vars[very_short_index] + 1,
        mother_vars[aniya_index] == height_vars[very_short_index] - 1
    ))
    
    # 14. Kailyn mother in third house.
    solver.add(mother_vars[kailyn_index] == 3)
    
    # Check satisfiability
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Create mapping from house number to attribute values
        house_data = {i: [] for i in range(1, 6)}
        
        # Helper function to get attribute value for a house
        def get_attr_value(house_num, attr_vars, attr_list):
            for idx, var in enumerate(attr_vars):
                if model.evaluate(var).as_long() == house_num:
                    return attr_list[idx]
            return None
        
        # Build rows for each house
        rows = []
        for house_num in range(1, 6):
            name_val = get_attr_value(house_num, name_vars, names)
            height_val = get_attr_value(house_num, height_vars, heights)
            mother_val = get_attr_value(house_num, mother_vars, mothers)
            hair_val = get_attr_value(house_num, hair_vars, hair_colors)
            rows.append([str(house_num), name_val, height_val, mother_val, hair_val])
        
        # Create JSON output
        output = {
            "solution": {
                "header": ["House", "Name", "Height", "Mother", "HairColor"],
                "rows": rows
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()