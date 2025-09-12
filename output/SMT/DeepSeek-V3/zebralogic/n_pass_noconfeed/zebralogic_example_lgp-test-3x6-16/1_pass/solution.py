import z3
import json

def main():
    # Create solver
    solver = z3.Solver()
    
    # Define houses
    houses = [1, 2, 3]
    
    # Define attributes with their possible values
    names = ['Eric', 'Peter', 'Arnold']
    drinks = ['tea', 'water', 'milk']
    nationalities = ['dane', 'brit', 'swede']
    educations = ['high school', 'associate', 'bachelor']
    house_styles = ['victorian', 'colonial', 'ranch']
    smoothies = ['cherry', 'watermelon', 'desert']
    
    # Create variables for each attribute in each house
    name_vars = [z3.Int(f'name_{h}') for h in houses]
    drink_vars = [z3.Int(f'drink_{h}') for h in houses]
    nationality_vars = [z3.Int(f'nationality_{h}') for h in houses]
    education_vars = [z3.Int(f'education_{h}') for h in houses]
    house_style_vars = [z3.Int(f'house_style_{h}') for h in houses]
    smoothie_vars = [z3.Int(f'smoothie_{h}') for h in houses]
    
    # Define domains for each variable
    for h in houses:
        solver.add(z3.And(name_vars[h-1] >= 0, name_vars[h-1] < len(names)))
        solver.add(z3.And(drink_vars[h-1] >= 0, drink_vars[h-1] < len(drinks)))
        solver.add(z3.And(nationality_vars[h-1] >= 0, nationality_vars[h-1] < len(nationalities)))
        solver.add(z3.And(education_vars[h-1] >= 0, education_vars[h-1] < len(educations)))
        solver.add(z3.And(house_style_vars[h-1] >= 0, house_style_vars[h-1] < len(house_styles)))
        solver.add(z3.And(smoothie_vars[h-1] >= 0, smoothie_vars[h-1] < len(smoothies)))
    
    # All attributes are distinct within their category
    solver.add(z3.Distinct(name_vars))
    solver.add(z3.Distinct(drink_vars))
    solver.add(z3.Distinct(nationality_vars))
    solver.add(z3.Distinct(education_vars))
    solver.add(z3.Distinct(house_style_vars))
    solver.add(z3.Distinct(smoothie_vars))
    
    # Clue 1: There is one house between Eric and the tea drinker.
    eric_index = names.index('Eric')
    tea_index = drinks.index('tea')
    for h in houses:
        if h + 2 <= max(houses):
            solver.add(z3.Or(
                z3.And(name_vars[h-1] == eric_index, drink_vars[h+1] == tea_index),
                z3.And(name_vars[h+1] == eric_index, drink_vars[h-1] == tea_index)
            ))
    
    # Clue 2: The person who likes milk is the person in a ranch-style home.
    milk_index = drinks.index('milk')
    ranch_index = house_styles.index('ranch')
    for h in houses:
        solver.add(z3.Implies(drink_vars[h-1] == milk_index, house_style_vars[h-1] == ranch_index))
        solver.add(z3.Implies(house_style_vars[h-1] == ranch_index, drink_vars[h-1] == milk_index))
    
    # Clue 3: The person with a bachelor's degree is in the second house.
    bachelor_index = educations.index('bachelor')
    solver.add(education_vars[1] == bachelor_index)
    
    # Clue 4: The person with a high school diploma is the Dane.
    hs_index = educations.index('high school')
    dane_index = nationalities.index('dane')
    for h in houses:
        solver.add(z3.Implies(education_vars[h-1] == hs_index, nationality_vars[h-1] == dane_index))
        solver.add(z3.Implies(nationality_vars[h-1] == dane_index, education_vars[h-1] == hs_index))
    
    # Clue 5: The Desert smoothie lover is the Swedish person.
    desert_index = smoothies.index('desert')
    swede_index = nationalities.index('swede')
    for h in houses:
        solver.add(z3.Implies(smoothie_vars[h-1] == desert_index, nationality_vars[h-1] == swede_index))
        solver.add(z3.Implies(nationality_vars[h-1] == swede_index, smoothie_vars[h-1] == desert_index))
    
    # Clue 6: The person residing in a Victorian house is not in the first house.
    victorian_index = house_styles.index('victorian')
    solver.add(house_style_vars[0] != victorian_index)
    
    # Clue 7: The person who likes Cherry smoothies is the person living in a colonial-style house.
    cherry_index = smoothies.index('cherry')
    colonial_index = house_styles.index('colonial')
    for h in houses:
        solver.add(z3.Implies(smoothie_vars[h-1] == cherry_index, house_style_vars[h-1] == colonial_index))
        solver.add(z3.Implies(house_style_vars[h-1] == colonial_index, smoothie_vars[h-1] == cherry_index))
    
    # Clue 8: Arnold is somewhere to the right of the person residing in a Victorian house.
    arnold_index = names.index('Arnold')
    for h_vic in houses:
        for h_arnold in houses:
            if h_arnold <= h_vic:
                solver.add(z3.Not(z3.And(
                    house_style_vars[h_vic-1] == victorian_index,
                    name_vars[h_arnold-1] == arnold_index
                )))
    
    # Clue 9: The person in a ranch-style home is the person with a high school diploma.
    for h in houses:
        solver.add(z3.Implies(house_style_vars[h-1] == ranch_index, education_vars[h-1] == hs_index))
        solver.add(z3.Implies(education_vars[h-1] == hs_index, house_style_vars[h-1] == ranch_index))
    
    # Check for solution
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Prepare solution data
        solution_data = {
            "solution": {
                "header": ["House", "Name", "Drink", "Nationality", "Education", "HouseStyle", "Smoothie"],
                "rows": []
            }
        }
        
        for h in houses:
            name_val = model.eval(name_vars[h-1]).as_long()
            drink_val = model.eval(drink_vars[h-1]).as_long()
            nationality_val = model.eval(nationality_vars[h-1]).as_long()
            education_val = model.eval(education_vars[h-1]).as_long()
            house_style_val = model.eval(house_style_vars[h-1]).as_long()
            smoothie_val = model.eval(smoothie_vars[h-1]).as_long()
            
            row = [
                str(h),
                names[name_val],
                drinks[drink_val],
                nationalities[nationality_val],
                educations[education_val],
                house_styles[house_style_val],
                smoothies[smoothie_val]
            ]
            solution_data["solution"]["rows"].append(row)
        
        # Output as JSON
        print(json.dumps(solution_data, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()