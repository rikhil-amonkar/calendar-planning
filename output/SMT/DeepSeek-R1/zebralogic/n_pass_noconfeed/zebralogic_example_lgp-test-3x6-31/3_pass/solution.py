import json
from z3 import *

def main():
    # Create solver
    solver = Solver()
    
    # Define houses by indices
    indices = [0, 1, 2]
    
    # Create enums for each category
    Name, (Eric, Peter, Arnold) = EnumSort('Name', ['Eric', 'Peter', 'Arnold'])
    Drink, (milk, water, tea) = EnumSort('Drink', ['milk', 'water', 'tea'])
    Vacation, (mountain, city, beach) = EnumSort('Vacation', ['mountain', 'city', 'beach'])
    HouseStyle, (colonial, victorian, ranch) = EnumSort('HouseStyle', ['colonial', 'victorian', 'ranch'])
    Animal, (cat, bird, horse) = EnumSort('Animal', ['cat', 'bird', 'horse'])
    Birthday, (jan, sept, april) = EnumSort('Birthday', ['jan', 'sept', 'april'])
    
    # Create variables for each house and attribute
    names = [Const(f'name_{i+1}', Name) for i in indices]
    drinks = [Const(f'drink_{i+1}', Drink) for i in indices]
    vacations = [Const(f'vacation_{i+1}', Vacation) for i in indices]
    styles = [Const(f'style_{i+1}', HouseStyle) for i in indices]
    animals = [Const(f'animal_{i+1}', Animal) for i in indices]
    birthdays = [Const(f'birthday_{i+1}', Birthday) for i in indices]
    
    # Add uniqueness constraints
    solver.add(Distinct(names))
    solver.add(Distinct(drinks))
    solver.add(Distinct(vacations))
    solver.add(Distinct(styles))
    solver.add(Distinct(animals))
    solver.add(Distinct(birthdays))
    
    # Clue 1: Colonial left of milk drinker
    colonial_pos = If(styles[0] == colonial, 1, If(styles[1] == colonial, 2, 3))
    milk_pos = If(drinks[0] == milk, 1, If(drinks[1] == milk, 2, 3))
    solver.add(colonial_pos < milk_pos)
    
    # Clue 2: City vacation directly left of Victorian house
    solver.add(Or(
        And(vacations[0] == city, styles[1] == victorian),
        And(vacations[1] == city, styles[2] == victorian)
    ))
    
    # Clue 3: January birthday directly left of cat lover
    solver.add(Or(
        And(birthdays[0] == jan, animals[1] == cat),
        And(birthdays[1] == jan, animals[2] == cat)
    ))
    
    # Clue 4: Water drinker is mountain vacationer
    for i in indices:
        solver.add(Implies(drinks[i] == water, vacations[i] == mountain))
    
    # Clue 5: Horse keeper is Peter
    for i in indices:
        solver.add(Implies(animals[i] == horse, names[i] == Peter))
    
    # Clue 6: Victorian house right of beach vacationer
    victorian_pos = If(styles[0] == victorian, 1, If(styles[1] == victorian, 2, 3))
    beach_pos = If(vacations[0] == beach, 1, If(vacations[1] == beach, 2, 3))
    solver.add(victorian_pos > beach_pos)
    
    # Clue 7: Peter prefers city breaks
    for i in indices:
        solver.add(Implies(names[i] == Peter, vacations[i] == city))
    
    # Clue 8: Mountain vacationer has April birthday
    for i in indices:
        solver.add(Implies(vacations[i] == mountain, birthdays[i] == april))
    
    # Clue 9: Eric drinks water
    for i in indices:
        solver.add(Implies(names[i] == Eric, drinks[i] == water))
    
    # Check solution
    if solver.check() == sat:
        model = solver.model()
        
        # Map house attributes to values
        result = []
        
        for i in indices:
            house_num = str(i + 1)
            # Directly convert evaluated expressions to strings
            name_val = str(model.evaluate(names[i]))
            drink_val = str(model.evaluate(drinks[i]))
            vacation_val = str(model.evaluate(vacations[i]))
            style_val = str(model.evaluate(styles[i]))
            animal_val = str(model.evaluate(animals[i]))
            birthday_val = str(model.evaluate(birthdays[i]))
            
            result.append([house_num, name_val, drink_val, vacation_val, style_val, animal_val, birthday_val])
        
        # Create JSON output
        output = {
            "solution": {
                "header": ["House", "Name", "Drink", "Vacation", "HouseStyle", "Animal", "Birthday"],
                "rows": result
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()