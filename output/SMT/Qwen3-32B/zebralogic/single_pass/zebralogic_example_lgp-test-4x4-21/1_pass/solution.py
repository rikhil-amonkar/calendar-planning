from z3 import *
import json

# Define EnumSorts for each category
Name, (Eric, Peter, Alice, Arnold) = EnumSort('Name', ['Eric', 'Peter', 'Alice', 'Arnold'])
CarModel, (tesla_model_3, honda_civic, toyota_camry, ford_f150) = EnumSort('CarModel', ['tesla_model_3', 'honda_civic', 'toyota_camry', 'ford_f150'])
Birthday, (jan, april, sept, feb) = EnumSort('Birthday', ['jan', 'april', 'sept', 'feb'])
Hobby, (painting, cooking, gardening, photography) = EnumSort('Hobby', ['painting', 'cooking', 'gardening', 'photography'])

# Create functions mapping each enum to house numbers (1-4)
name_house = Function('name_house', Name, IntSort())
car_house = Function('car_house', CarModel, IntSort())
birthday_house = Function('birthday_house', Birthday, IntSort())
hobby_house = Function('hobby_house', Hobby, IntSort())

solver = Solver()

# Add constraints for AllDifferent for each category
solver.add(Distinct([name_house(n) for n in [Eric, Peter, Alice, Arnold]]))
solver.add(Distinct([car_house(c) for c in [tesla_model_3, honda_civic, toyota_camry, ford_f150]]))
solver.add(Distinct([birthday_house(b) for b in [jan, april, sept, feb]]))
solver.add(Distinct([hobby_house(h) for h in [painting, cooking, gardening, photography]]))

# Add constraints for house numbers to be between 1 and 4
for n in [Eric, Peter, Alice, Arnold]:
    solver.add(And(1 <= name_house(n), name_house(n) <= 4))

for c in [tesla_model_3, honda_civic, toyota_camry, ford_f150]:
    solver.add(And(1 <= car_house(c), car_house(c) <= 4))

for b in [jan, april, sept, feb]:
    solver.add(And(1 <= birthday_house(b), birthday_house(b) <= 4))

for h in [painting, cooking, gardening, photography]:
    solver.add(And(1 <= hobby_house(h), hobby_house(h) <= 4))

# Add the clues as constraints
solver.add(birthday_house(jan) != 2)  # Clue 1
solver.add(hobby_house(photography) < name_house(Eric))  # Clue 2
solver.add(hobby_house(photography) < name_house(Peter))  # Clue 3
solver.add(car_house(honda_civic) + 1 == car_house(tesla_model_3))  # Clue 4
solver.add(Or(
    car_house(tesla_model_3) - hobby_house(gardening) == 2,
    hobby_house(gardening) - car_house(tesla_model_3) == 2
))  # Clue 5
solver.add(car_house(tesla_model_3) == name_house(Arnold))  # Clue 6
solver.add(birthday_house(feb) == hobby_house(cooking))  # Clue 7
solver.add(car_house(toyota_camry) == name_house(Peter))  # Clue 8
solver.add(birthday_house(april) == name_house(Arnold))  # Clue 9
solver.add(hobby_house(photography) == name_house(Alice))  # Clue 10
solver.add(birthday_house(jan) == name_house(Peter))  # Clue 11

# Check for solution
if solver.check() == sat:
    model = solver.model()
    solution = []
    for house_num in range(1, 5):
        # Find the name in this house
        name = None
        for n in [Eric, Peter, Alice, Arnold]:
            val = model.eval(name_house(n))
            if is_int_value(val) and val.as_long() == house_num:
                name = n
                break
        # Find the car model
        car = None
        for c in [tesla_model_3, honda_civic, toyota_camry, ford_f150]:
            val = model.eval(car_house(c))
            if is_int_value(val) and val.as_long() == house_num:
                car = c
                break
        # Find the birthday
        birthday = None
        for b in [jan, april, sept, feb]:
            val = model.eval(birthday_house(b))
            if is_int_value(val) and val.as_long() == house_num:
                birthday = b
                break
        # Find the hobby
        hobby = None
        for h in [painting, cooking, gardening, photography]:
            val = model.eval(hobby_house(h))
            if is_int_value(val) and val.as_long() == house_num:
                hobby = h
                break
        # Convert enum names to problem format
        name_str = name.decl().name()
        car_str = car.decl().name().replace("_", " ")
        birthday_str = birthday.decl().name()
        hobby_str = hobby.decl().name()
        solution.append([str(house_num), name_str, car_str, birthday_str, hobby_str])
    # Output JSON
    print(json.dumps({
        "solution": {
            "header": ["House", "Name", "CarModel", "Birthday", "Hobby"],
            "rows": solution
        }
    }, indent=2))
else:
    print("No solution found.")