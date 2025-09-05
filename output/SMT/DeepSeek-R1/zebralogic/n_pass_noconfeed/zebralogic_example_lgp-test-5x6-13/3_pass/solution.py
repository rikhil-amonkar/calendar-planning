import json
from z3 import *

def main():
    # Create the solver
    s = Solver()

    # Define the attributes and their possible values
    names = ['Eric', 'Peter', 'Arnold', 'Alice', 'Bob']
    foods = ['stir fry', 'spaghetti', 'stew', 'grilled cheese', 'pizza']
    car_models = ['ford f150', 'tesla model 3', 'bmw 3 series', 'toyota camry', 'honda civic']
    phone_models = ['iphone 13', 'google pixel 6', 'samsung galaxy s21', 'oneplus 9', 'huawei p50']
    occupations = ['teacher', 'lawyer', 'doctor', 'artist', 'engineer']
    drinks = ['tea', 'milk', 'water', 'root beer', 'coffee']

    # Create enumerations for each attribute type
    Name, (Eric, Peter, Arnold, Alice, Bob) = EnumSort('Name', names)
    Food, (StirFry, Spaghetti, Stew, GrilledCheese, Pizza) = EnumSort('Food', foods)
    CarModel, (FordF150, TeslaModel3, BMW3Series, ToyotaCamry, HondaCivic) = EnumSort('CarModel', car_models)
    PhoneModel, (IPhone13, GooglePixel6, SamsungGalaxyS21, OnePlus9, HuaweiP50) = EnumSort('PhoneModel', phone_models)
    Occupation, (Teacher, Lawyer, Doctor, Artist, Engineer) = EnumSort('Occupation', occupations)
    Drink, (Tea, Milk, Water, RootBeer, Coffee) = EnumSort('Drink', drinks)

    # Create variables for each attribute in each house
    houses = [0, 1, 2, 3, 4]  # Now using 0-indexed indices
    name = [Const(f'name_{i}', Name) for i in houses]
    food = [Const(f'food_{i}', Food) for i in houses]
    car = [Const(f'car_{i}', CarModel) for i in houses]
    phone = [Const(f'phone_{i}', PhoneModel) for i in houses]
    occupation = [Const(f'occupation_{i}', Occupation) for i in houses]
    drink = [Const(f'drink_{i}', Drink) for i in houses]

    # Add constraint: all attributes must have distinct values
    s.add(Distinct(name))
    s.add(Distinct(food))
    s.add(Distinct(car))
    s.add(Distinct(phone))
    s.add(Distinct(occupation))
    s.add(Distinct(drink))

    # Clue 1: The root beer lover is the person who owns a Honda Civic.
    for i in houses:
        s.add(Implies(drink[i] == RootBeer, car[i] == HondaCivic))

    # Clue 2: The person who likes milk is directly left of the person who loves eating grilled cheese.
    for i in range(1, 5):
        s.add(Implies(drink[i-1] == Milk, food[i] == GrilledCheese))
    s.add(Or([And(drink[i-1] == Milk, food[i] == GrilledCheese) for i in range(1, 5)]))

    # Clue 3: Alice is the person who uses a Samsung Galaxy S21.
    for i in houses:
        s.add(Implies(name[i] == Alice, phone[i] == SamsungGalaxyS21))

    # Clue 4: Alice is the person who loves stir fry.
    for i in houses:
        s.add(Implies(name[i] == Alice, food[i] == StirFry))

    # Clue 5: The tea drinker is not in the fifth house.
    s.add(drink[4] != Tea)

    # Clue 6: The person who owns a BMW 3 Series is somewhere to the left of the tea drinker.
    s.add(Or([And(i < j, car[i] == BMW3Series, drink[j] == Tea) for i in houses for j in houses if i < j]))

    # Clue 7: The person who is a doctor is Arnold.
    for i in houses:
        s.add(Implies(occupation[i] == Doctor, name[i] == Arnold))

    # Clue 8: The person who uses an iPhone 13 is the coffee drinker.
    for i in houses:
        s.add(Implies(phone[i] == IPhone13, drink[i] == Coffee))

    # Clue 9: The person who is an engineer is the person who owns a BMW 3 Series.
    for i in houses:
        s.add(Implies(occupation[i] == Engineer, car[i] == BMW3Series))

    # Clue 10: The person who loves the stew is the person who uses an iPhone 13.
    for i in houses:
        s.add(Implies(food[i] == Stew, phone[i] == IPhone13))

    # Clue 11: The person who is a doctor is directly left of the person who uses a OnePlus 9.
    for i in range(1, 5):
        s.add(Implies(occupation[i-1] == Doctor, phone[i] == OnePlus9))
    s.add(Or([And(occupation[i-1] == Doctor, phone[i] == OnePlus9) for i in range(1, 5)]))

    # Clue 12: The person who owns a Honda Civic is directly left of the person who loves the spaghetti eater.
    for i in range(1, 5):
        s.add(Implies(car[i-1] == HondaCivic, food[i] == Spaghetti))
    s.add(Or([And(car[i-1] == HondaCivic, food[i] == Spaghetti) for i in range(1, 5)]))

    # Clue 13: The person who uses a Google Pixel 6 is the tea drinker.
    for i in houses:
        s.add(Implies(phone[i] == GooglePixel6, drink[i] == Tea))

    # Clue 14: Alice is the person who is an artist.
    for i in houses:
        s.add(Implies(name[i] == Alice, occupation[i] == Artist))

    # Clue 15: There is one house between Alice and the person who owns a Ford F-150.
    s.add(Or(
        And(name[0] == Alice, car[2] == FordF150),
        And(name[1] == Alice, car[3] == FordF150),
        And(name[2] == Alice, Or(car[0] == FordF150, car[4] == FordF150)),
        And(name[3] == Alice, car[1] == FordF150),
        And(name[4] == Alice, car[2] == FordF150)
    ))

    # Clue 16: Arnold is the person who owns a Toyota Camry.
    for i in houses:
        s.add(Implies(name[i] == Arnold, car[i] == ToyotaCamry))

    # Clue 17: Eric is in the fourth house.
    s.add(name[3] == Eric)

    # Clue 18: The person who uses a OnePlus 9 is the person who is a lawyer.
    for i in houses:
        s.add(Implies(phone[i] == OnePlus9, occupation[i] == Lawyer))

    # Clue 19: The person who loves eating grilled cheese is Peter.
    for i in houses:
        s.add(Implies(food[i] == GrilledCheese, name[i] == Peter))

    # Check for a solution
    if s.check() == sat:
        model = s.model()
        result = []
        for i in range(5):
            n = model.eval(name[i])
            f = model.eval(food[i])
            c = model.eval(car[i])
            p = model.eval(phone[i])
            o = model.eval(occupation[i])
            d = model.eval(drink[i])
            # Convert Z3 symbols to strings using model evaluation
            name_val = [names[j] for j in range(5) if is_true(model.eval(n == [Eric, Peter, Arnold, Alice, Bob][j]))][0]
            food_val = [foods[j] for j in range(5) if is_true(model.eval(f == [StirFry, Spaghetti, Stew, GrilledCheese, Pizza][j]))][0]
            car_val = [car_models[j] for j in range(5) if is_true(model.eval(c == [FordF150, TeslaModel3, BMW3Series, ToyotaCamry, HondaCivic][j]))][0]
            phone_val = [phone_models[j] for j in range(5) if is_true(model.eval(p == [IPhone13, GooglePixel6, SamsungGalaxyS21, OnePlus9, HuaweiP50][j]))][0]
            occupation_val = [occupations[j] for j in range(5) if is_true(model.eval(o == [Teacher, Lawyer, Doctor, Artist, Engineer][j]))][0]
            drink_val = [drinks[j] for j in range(5) if is_true(model.eval(d == [Tea, Milk, Water, RootBeer, Coffee][j]))][0]
            row = [
                str(i+1),
                name_val,
                food_val,
                car_val,
                phone_val,
                occupation_val,
                drink_val
            ]
            result.append(row)
        
        output = {
            "solution": {
                "header": ["House", "Name", "Food", "CarModel", "PhoneModel", "Occupation", "Drink"],
                "rows": result
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()