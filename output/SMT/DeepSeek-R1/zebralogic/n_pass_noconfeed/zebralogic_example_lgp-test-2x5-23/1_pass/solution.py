import z3
import json

def main():
    # Create a solver instance
    solver = z3.Solver()

    # Define the attributes using EnumSort
    Name = z3.EnumSort('Name', ['Arnold', 'Eric'])
    Education = z3.EnumSort('Education', ['associate', 'high_school'])
    Height = z3.EnumSort('Height', ['short', 'very_short'])
    Food = z3.EnumSort('Food', ['grilled_cheese', 'pizza'])
    Drink = z3.EnumSort('Drink', ['tea', 'water'])

    # Create constants for each attribute value
    Arnold, Eric = Name.consts()
    associate, high_school = Education.consts()
    short, very_short = Height.consts()
    grilled_cheese, pizza = Food.consts()
    tea, water = Drink.consts()

    # Create variables for each house's attributes
    names = [z3.Const(f'name_{i}', Name) for i in range(1, 3)]
    educations = [z3.Const(f'edu_{i}', Education) for i in range(1, 3)]
    heights = [z3.Const(f'height_{i}', Height) for i in range(1, 3)]
    foods = [z3.Const(f'food_{i}', Food) for i in range(1, 3)]
    drinks = [z3.Const(f'drink_{i}', Drink) for i in range(1, 3)]

    # Add constraints that all attributes are unique within their category
    solver.add(z3.Distinct(names))
    solver.add(z3.Distinct(educations))
    solver.add(z3.Distinct(heights))
    solver.add(z3.Distinct(foods))
    solver.add(z3.Distinct(drinks))

    # Clue 1: The person who is very short is the person who is a pizza lover.
    for i in range(2):
        solver.add(z3.Implies(heights[i] == very_short, foods[i] == pizza))

    # Clue 2: The person who loves eating grilled cheese is in the second house.
    solver.add(foods[1] == grilled_cheese)

    # Clue 3: The person with a high school diploma is the person who is a pizza lover.
    for i in range(2):
        solver.add(z3.Implies(educations[i] == high_school, foods[i] == pizza))

    # Clue 4: The tea drinker is the person who loves eating grilled cheese.
    for i in range(2):
        solver.add(z3.Implies(drinks[i] == tea, foods[i] == grilled_cheese))

    # Clue 5: Arnold is the person who is a pizza lover.
    for i in range(2):
        solver.add(z3.Implies(names[i] == Arnold, foods[i] == pizza))

    # Check if the solver is satisfied
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Prepare the result structure
        header = ["House", "Name", "Education", "Height", "Food", "Drink"]
        rows = []
        
        for i in range(2):
            # Evaluate each attribute for the current house
            name_val = model.eval(names[i])
            edu_val = model.eval(educations[i])
            height_val = model.eval(heights[i])
            food_val = model.eval(foods[i])
            drink_val = model.eval(drinks[i])
            
            # Convert Z3 symbols to strings and replace underscores with spaces
            name_str = str(name_val).replace('_', ' ')
            edu_str = str(edu_val).replace('_', ' ')
            height_str = str(height_val).replace('_', ' ')
            food_str = str(food_val).replace('_', ' ')
            drink_str = str(drink_val).replace('_', ' ')
            
            rows.append([str(i+1), name_str, edu_str, height_str, food_str, drink_str])
        
        # Create the JSON output
        output = {
            "solution": {
                "header": header,
                "rows": rows
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()