import z3
import json

def main():
    # Create solver
    solver = z3.Solver()
    
    # Define houses
    houses = [1, 2]
    
    # Define attributes
    names = ['Arnold', 'Eric']
    educations = ['associate', 'high school']
    heights = ['short', 'very short']
    foods = ['grilled cheese', 'pizza']
    drinks = ['tea', 'water']
    
    # Create variables for each attribute per house
    name_vars = {h: z3.Int(f'name_{h}') for h in houses}
    education_vars = {h: z3.Int(f'education_{h}') for h in houses}
    height_vars = {h: z3.Int(f'height_{h}') for h in houses}
    food_vars = {h: z3.Int(f'food_{h}') for h in houses}
    drink_vars = {h: z3.Int(f'drink_{h}') for h in houses}
    
    # Define domains for each attribute
    for h in houses:
        solver.add(z3.And(name_vars[h] >= 0, name_vars[h] < len(names)))
        solver.add(z3.And(education_vars[h] >= 0, education_vars[h] < len(educations)))
        solver.add(z3.And(height_vars[h] >= 0, height_vars[h] < len(heights)))
        solver.add(z3.And(food_vars[h] >= 0, food_vars[h] < len(foods)))
        solver.add(z3.And(drink_vars[h] >= 0, drink_vars[h] < len(drinks)))
    
    # All attributes must be unique within their category
    solver.add(z3.Distinct([name_vars[h] for h in houses]))
    solver.add(z3.Distinct([education_vars[h] for h in houses]))
    solver.add(z3.Distinct([height_vars[h] for h in houses]))
    solver.add(z3.Distinct([food_vars[h] for h in houses]))
    solver.add(z3.Distinct([drink_vars[h] for h in houses]))
    
    # Clue 1: The person who is very short is the person who is a pizza lover.
    very_short_idx = heights.index('very short')
    pizza_idx = foods.index('pizza')
    for h in houses:
        solver.add(z3.Implies(height_vars[h] == very_short_idx, food_vars[h] == pizza_idx))
    
    # Clue 2: The person who loves eating grilled cheese is in the second house.
    grilled_cheese_idx = foods.index('grilled cheese')
    solver.add(food_vars[2] == grilled_cheese_idx)
    
    # Clue 3: The person with a high school diploma is the person who is a pizza lover.
    high_school_idx = educations.index('high school')
    for h in houses:
        solver.add(z3.Implies(education_vars[h] == high_school_idx, food_vars[h] == pizza_idx))
    
    # Clue 4: The tea drinker is the person who loves eating grilled cheese.
    tea_idx = drinks.index('tea')
    for h in houses:
        solver.add(z3.Implies(drink_vars[h] == tea_idx, food_vars[h] == grilled_cheese_idx))
    
    # Clue 5: Arnold is the person who is a pizza lover.
    arnold_idx = names.index('Arnold')
    for h in houses:
        solver.add(z3.Implies(name_vars[h] == arnold_idx, food_vars[h] == pizza_idx))
    
    # Check if solution exists
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Prepare result
        result = {
            "solution": {
                "header": ["House", "Name", "Education", "Height", "Food", "Drink"],
                "rows": []
            }
        }
        
        for house in sorted(houses):
            name_idx = model.evaluate(name_vars[house]).as_long()
            education_idx = model.evaluate(education_vars[house]).as_long()
            height_idx = model.evaluate(height_vars[house]).as_long()
            food_idx = model.evaluate(food_vars[house]).as_long()
            drink_idx = model.evaluate(drink_vars[house]).as_long()
            
            row = [
                str(house),
                names[name_idx],
                educations[education_idx],
                heights[height_idx],
                foods[food_idx],
                drinks[drink_idx]
            ]
            result["solution"]["rows"].append(row)
        
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()