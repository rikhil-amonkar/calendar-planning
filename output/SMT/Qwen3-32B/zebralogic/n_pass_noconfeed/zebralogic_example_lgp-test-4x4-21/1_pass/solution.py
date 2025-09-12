import json
from z3 import *

def main():
    # Define EnumSorts
    Name, (Eric, Peter, Alice, Arnold) = EnumSort('Name', ['Eric', 'Peter', 'Alice', 'Arnold'])
    Car, (Tesla, Honda, Toyota, Ford) = EnumSort('Car', ['tesla_model_3', 'honda_civic', 'toyota_camry', 'ford_f150'])
    Birthday, (Jan, April, Sept, Feb) = EnumSort('Birthday', ['jan', 'april', 'sept', 'feb'])
    Hobby, (Painting, Cooking, Gardening, Photography) = EnumSort('Hobby', ['painting', 'cooking', 'gardening', 'photography'])

    # Create variables for each house (1-4)
    names = [Const(f'name_{i+1}', Name) for i in range(4)]
    cars = [Const(f'car_{i+1}', Car) for i in range(4)]
    birthdays = [Const(f'birthday_{i+1}', Birthday) for i in range(4)]
    hobbies = [Const(f'hobby_{i+1}', Hobby) for i in range(4)]

    s = Solver()

    # Add distinct constraints
    s.add(Distinct(names))
    s.add(Distinct(cars))
    s.add(Distinct(birthdays))
    s.add(Distinct(hobbies))

    # Clue 1: birthday_2 != jan
    s.add(birthdays[1] != Jan)

    # Clue 2 and 3: photography is left of Eric and Peter
    pos_photography = Sum([ If(hobbies[i] == Photography, IntVal(i+1), IntVal(0)) for i in range(4) ])
    pos_eric = Sum([ If(names[i] == Eric, IntVal(i+1), IntVal(0)) for i in range(4) ])
    pos_peter = Sum([ If(names[i] == Peter, IntVal(i+1), IntVal(0)) for i in range(4) ])
    s.add(pos_photography < pos_eric)
    s.add(pos_photography < pos_peter)

    # Clue 4: Honda directly left of Tesla
    s.add(Or(
        And(cars[0] == Honda, cars[1] == Tesla),
        And(cars[1] == Honda, cars[2] == Tesla),
        And(cars[2] == Honda, cars[3] == Tesla)
    ))

    # Clue 5: one house between Tesla and gardening
    pos_tesla = Sum([ If(cars[i] == Tesla, IntVal(i+1), IntVal(0)) for i in range(4) ])
    pos_gardening = Sum([ If(hobbies[i] == Gardening, IntVal(i+1), IntVal(0)) for i in range(4) ])
    s.add(Or(pos_gardening == pos_tesla + 2, pos_gardening == pos_tesla - 2))

    # Clues 6-11 (per house)
    for i in range(4):
        # Clue 6: Tesla owner is Arnold
        s.add(Implies(cars[i] == Tesla, names[i] == Arnold))
        # Clue 7: birthday feb is cooking
        s.add(Implies(birthdays[i] == Feb, hobbies[i] == Cooking))
        # Clue 8: Toyota is Peter
        s.add(Implies(cars[i] == Toyota, names[i] == Peter))
        # Clue 9: birthday april is Arnold
        s.add(Implies(birthdays[i] == April, names[i] == Arnold))
        # Clue 10: Alice is photography
        s.add(Implies(hobbies[i] == Photography, names[i] == Alice))
        # Clue 11: Peter's birthday is jan
        s.add(Implies(names[i] == Peter, birthdays[i] == Jan))

    # Check for solution
    if s.check() == sat:
        model = s.model()
        # Prepare the solution data
        car_mapping = {
            'tesla_model_3': 'tesla model 3',
            'honda_civic': 'honda civic',
            'toyota_camry': 'toyota camry',
            'ford_f150': 'ford f150'
        }
        rows = []
        for i in range(4):
            house_num = i + 1
            name = model.eval(names[i]).decl().name()
            car_enum = model.eval(cars[i]).decl().name()
            car = car_mapping[car_enum]
            birthday = model.eval(birthdays[i]).decl().name()
            hobby = model.eval(hobbies[i]).decl().name()
            rows.append([str(house_num), name, car, birthday, hobby])
        solution = {
            "solution": {
                "header": ["House", "Name", "CarModel", "Birthday", "Hobby"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()