import json
from z3 import *

def main():
    # Define the attributes
    names = ['Eric', 'Peter', 'Alice', 'Arnold']
    cars = ['tesla model 3', 'honda civic', 'toyota camry', 'ford f150']
    birthdays = ['jan', 'april', 'sept', 'feb']
    hobbies = ['painting', 'cooking', 'gardening', 'photography']
    
    # Create Z3 enums for each attribute
    Name = EnumSort('Name', names)
    Car = EnumSort('Car', cars)
    Birthday = EnumSort('Birthday', birthdays)
    Hobby = EnumSort('Hobby', hobbies)
    
    # Create variables for each house
    n = [Const(f'n_{i}', Name) for i in range(4)]
    c = [Const(f'c_{i}', Car) for i in range(4)]
    b = [Const(f'b_{i}', Birthday) for i in range(4)]
    h = [Const(f'h_{i}', Hobby) for i in range(4)]
    
    s = Solver()
    
    # All attributes are distinct
    s.add(Distinct(n))
    s.add(Distinct(c))
    s.add(Distinct(b))
    s.add(Distinct(h))
    
    # Extract constants for easier reference
    Eric, Peter, Alice, Arnold = [Name.names[i] for i in range(4)]
    tesla, honda, toyota, ford = [Car.cars[i] for i in range(4)]
    jan, april, sept, feb = [Birthday.birthdays[i] for i in range(4)]
    painting, cooking, gardening, photography = [Hobby.hobbies[i] for i in range(4)]
    
    # Clue 1: January birthday not in second house
    s.add(b[1] != jan)
    
    # Clue 2: Photography left of Eric
    s.add(Or([And(h[i] == photography, Any([n[j] == Eric for j in range(i+1, 4)])) for i in range(3)]))
    
    # Clue 3: Photography left of Peter
    s.add(Or([And(h[i] == photography, Any([n[j] == Peter for j in range(i+1, 4)])) for i in range(3)]))
    
    # Clue 4: Honda Civic directly left of Tesla Model 3
    s.add(Or([And(c[i] == honda, c[i+1] == tesla) for i in range(3)]))
    
    # Clue 5: One house between Tesla and Gardening
    s.add(Or(
        Or([And(c[i] == tesla, h[i+2] == gardening) for i in range(2)]),
        Or([And(h[i] == gardening, c[i+2] == tesla) for i in range(2)])
    ))
    
    # Clue 6: Tesla owner is Arnold
    for i in range(4):
        s.add(Implies(c[i] == tesla, n[i] == Arnold))
    
    # Clue 7: February birthday loves cooking
    for i in range(4):
        s.add(Implies(b[i] == feb, h[i] == cooking))
    
    # Clue 8: Toyota Camry owner is Peter
    for i in range(4):
        s.add(Implies(c[i] == toyota, n[i] == Peter))
    
    # Clue 9: April birthday is Arnold
    for i in range(4):
        s.add(Implies(b[i] == april, n[i] == Arnold))
    
    # Clue 10: Alice is photography enthusiast
    for i in range(4):
        s.add(Implies(n[i] == Alice, h[i] == photography))
    
    # Clue 11: Peter has January birthday
    for i in range(4):
        s.add(Implies(n[i] == Peter, b[i] == jan))
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        
        # Map Z3 values back to strings
        name_map = {getattr(Name, name): name for name in names}
        car_map = {getattr(Car, car): car for car in cars}
        birthday_map = {getattr(Birthday, bd): bd for bd in birthdays}
        hobby_map = {getattr(Hobby, hb): hb for hb in hobbies}
        
        rows = []
        for i in range(4):
            house_num = str(i + 1)
            name_val = name_map[model.eval(n[i])]
            car_val = car_map[model.eval(c[i])]
            birthday_val = birthday_map[model.eval(b[i])]
            hobby_val = hobby_map[model.eval(h[i])]
            rows.append([house_num, name_val, car_val, birthday_val, hobby_val])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "CarModel", "Birthday", "Hobby"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()