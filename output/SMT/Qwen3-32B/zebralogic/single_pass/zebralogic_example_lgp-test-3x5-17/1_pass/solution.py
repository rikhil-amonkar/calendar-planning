from z3 import *
import json

# Define EnumSorts for each category
Name, (Eric, Arnold, Peter) = EnumSort('Name', ['Eric', 'Arnold', 'Peter'])
PhoneModel, (Iphone13, SamsungS21, GooglePixel6) = EnumSort('PhoneModel', ['iphone_13', 'samsung_galaxy_s21', 'google_pixel_6'])
Height, (VeryShort, Average, Short) = EnumSort('Height', ['very_short', 'average', 'short'])
HouseStyle, (Colonial, Ranch, Victorian) = EnumSort('HouseStyle', ['colonial', 'ranch', 'victorian'])
CarModel, (TeslaModel3, ToyotaCamry, FordF150) = EnumSort('CarModel', ['tesla_model_3', 'toyota_camry', 'ford_f150'])

# Create variables for each house
# House 1
name1 = Const('name1', Name)
phone1 = Const('phone1', PhoneModel)
height1 = Const('height1', Height)
style1 = Const('style1', HouseStyle)
car1 = Const('car1', CarModel)

# House 2
name2 = Const('name2', Name)
phone2 = Const('phone2', PhoneModel)
height2 = Const('height2', Height)
style2 = Const('style2', HouseStyle)
car2 = Const('car2', CarModel)

# House 3
name3 = Const('name3', Name)
phone3 = Const('phone3', PhoneModel)
height3 = Const('height3', Height)
style3 = Const('style3', HouseStyle)
car3 = Const('car3', CarModel)

solver = Solver()

# Add distinct constraints for each attribute
solver.add(Distinct(name1, name2, name3))
solver.add(Distinct(phone1, phone2, phone3))
solver.add(Distinct(height1, height2, height3))
solver.add(Distinct(style1, style2, style3))
solver.add(Distinct(car1, car2, car3))

# Add clues as constraints
# Clue 2: colonial in house 2
solver.add(style2 == Colonial)

# Clue 7: Arnold in house 2
solver.add(name2 == Arnold)

# Clue 9: average height in house 1
solver.add(height1 == Average)

# Clue 6: ranch is to the left of colonial (so style1 is ranch)
solver.add(style1 == Ranch)

# Clue 3: Tesla owner is very short
solver.add(Implies(car1 == TeslaModel3, height1 == VeryShort))
solver.add(Implies(car2 == TeslaModel3, height2 == VeryShort))
solver.add(Implies(car3 == TeslaModel3, height3 == VeryShort))

# Clue 4: short person directly left of Samsung
solver.add(Or(
    And(height1 == Short, phone2 == SamsungS21),
    And(height2 == Short, phone3 == SamsungS21)
))

# Clue 5: iPhone directly left of Google Pixel
solver.add(Or(
    And(phone1 == Iphone13, phone2 == GooglePixel6),
    And(phone2 == Iphone13, phone3 == GooglePixel6)
))

# Clue 1: Peter is to the right of Eric
solver.add(Or(name1 != Eric, Or(name2 == Peter, name3 == Peter)))
solver.add(Or(name2 != Eric, name3 == Peter))
solver.add(Or(name3 != Eric))

# Clue 8: Ford is to the right of Toyota
solver.add(Or(car1 != ToyotaCamry, Or(car2 == FordF150, car3 == FordF150)))
solver.add(Or(car2 != ToyotaCamry, car3 == FordF150))
solver.add(Or(car3 != ToyotaCamry))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    # Extract values for each house
    houses = []
    for i, (n, p, h, s, c) in enumerate([
        (name1, phone1, height1, style1, car1),
        (name2, phone2, height2, style2, car2),
        (name3, phone3, height3, style3, car3)
    ]):
        # Convert Enum to string
        name = model.eval(n).decl().name()
        phone = model.eval(p).decl().name()
        height = model.eval(h).decl().name()
        style = model.eval(s).decl().name()
        car = model.eval(c).decl().name()
        houses.append([str(i+1), name, phone, height, style, car])
    
    # Format as required JSON
    solution = {
        "solution": {
            "header": ["House", "Name", "PhoneModel", "Height", "HouseStyle", "CarModel"],
            "rows": houses
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")