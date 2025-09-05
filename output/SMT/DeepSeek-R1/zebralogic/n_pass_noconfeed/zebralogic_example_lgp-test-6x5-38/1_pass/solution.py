from z3 import *
import json

def main():
    # Define the sorts for each attribute
    Name, (Arnold, Carol, Eric, Bob, Alice, Peter) = EnumSort('Name', ['Arnold', 'Carol', 'Eric', 'Bob', 'Alice', 'Peter'])
    Birthday, (feb, mar, sept, jan, may, april) = EnumSort('Birthday', ['feb', 'mar', 'sept', 'jan', 'may', 'april'])
    Food, (stew, soup, grilled_cheese, stir_fry, spaghetti, pizza) = EnumSort('Food', ['stew', 'soup', 'grilled cheese', 'stir fry', 'spaghetti', 'pizza'])
    Height, (very_short, average, super_tall, short, very_tall, tall) = EnumSort('Height', ['very short', 'average', 'super tall', 'short', 'very tall', 'tall'])
    CarModel, (chevrolet_silverado, ford_f150, bmw_3_series, tesla_model_3, toyota_camry, honda_civic) = EnumSort('CarModel', ['chevrolet silverado', 'ford f150', 'bmw 3 series', 'tesla model 3', 'toyota camry', 'honda civic'])

    # Arrays for each house attribute
    names = [Const(f'name_{i}', Name) for i in range(6)]
    birthdays = [Const(f'birthday_{i}', Birthday) for i in range(6)]
    foods = [Const(f'food_{i}', Food) for i in range(6)]
    heights = [Const(f'height_{i}', Height) for i in range(6)]
    cars = [Const(f'car_{i}', CarModel) for i in range(6)]

    # Solver
    s = Solver()

    # Distinct constraints for each attribute
    s.add(Distinct(names))
    s.add(Distinct(birthdays))
    s.add(Distinct(foods))
    s.add(Distinct(heights))
    s.add(Distinct(cars))

    # Define integer variables for specific attributes
    eric_house = Int('eric_house')
    carol_house = Int('carol_house')
    alice_house = Int('alice_house')
    bob_house = Int('bob_house')
    peter_house = Int('peter_house')
    may_birthday_house = Int('may_birthday_house')
    april_birthday_house = Int('april_birthday_house')
    march_birthday_house = Int('march_birthday_house')
    sept_birthday_house = Int('sept_birthday_house')
    stir_fry_house = Int('stir_fry_house')
    pizza_house = Int('pizza_house')
    soup_house = Int('soup_house')
    spaghetti_house = Int('spaghetti_house')
    stew_house = Int('stew_house')
    very_short_house = Int('very_short_house')
    average_house = Int('average_house')
    super_tall_house = Int('super_tall_house')
    short_house = Int('short_house')
    very_tall_house = Int('very_tall_house')
    tall_house = Int('tall_house')
    bmw_house = Int('bmw_house')
    tesla_house = Int('tesla_house')
    toyota_house = Int('toyota_house')
    honda_house = Int('honda_house')
    ford_house = Int('ford_house')
    chevrolet_house = Int('chevrolet_house')

    # Constrain integer variables to valid houses
    house_vars = [eric_house, carol_house, alice_house, bob_house, peter_house,
                  may_birthday_house, april_birthday_house, march_birthday_house, sept_birthday_house,
                  stir_fry_house, pizza_house, soup_house, spaghetti_house, stew_house,
                  very_short_house, average_house, super_tall_house, short_house, very_tall_house, tall_house,
                  bmw_house, tesla_house, toyota_house, honda_house, ford_house, chevrolet_house]
    for var in house_vars:
        s.add(var >= 0, var < 6)

    # Connect integer variables to attribute arrays
    for i in range(6):
        s.add(If(names[i] == Eric, eric_house == i, True))
        s.add(If(names[i] == Carol, carol_house == i, True))
        s.add(If(names[i] == Alice, alice_house == i, True))
        s.add(If(names[i] == Bob, bob_house == i, True))
        s.add(If(names[i] == Peter, peter_house == i, True))

        s.add(If(birthdays[i] == may, may_birthday_house == i, True))
        s.add(If(birthdays[i] == april, april_birthday_house == i, True))
        s.add(If(birthdays[i] == mar, march_birthday_house == i, True))
        s.add(If(birthdays[i] == sept, sept_birthday_house == i, True))

        s.add(If(foods[i] == stir_fry, stir_fry_house == i, True))
        s.add(If(foods[i] == pizza, pizza_house == i, True))
        s.add(If(foods[i] == soup, soup_house == i, True))
        s.add(If(foods[i] == spaghetti, spaghetti_house == i, True))
        s.add(If(foods[i] == stew, stew_house == i, True))

        s.add(If(heights[i] == very_short, very_short_house == i, True))
        s.add(If(heights[i] == average, average_house == i, True))
        s.add(If(heights[i] == super_tall, super_tall_house == i, True))
        s.add(If(heights[i] == short, short_house == i, True))
        s.add(If(heights[i] == very_tall, very_tall_house == i, True))
        s.add(If(heights[i] == tall, tall_house == i, True))

        s.add(If(cars[i] == bmw_3_series, bmw_house == i, True))
        s.add(If(cars[i] == tesla_model_3, tesla_house == i, True))
        s.add(If(cars[i] == toyota_camry, toyota_house == i, True))
        s.add(If(cars[i] == honda_civic, honda_house == i, True))
        s.add(If(cars[i] == ford_f150, ford_house == i, True))
        s.add(If(cars[i] == chevrolet_silverado, chevrolet_house == i, True))

    # Clue 1: Honda Civic owner is short
    for i in range(6):
        s.add(If(cars[i] == honda_civic, heights[i] == short, True))
        s.add(If(heights[i] == short, cars[i] == honda_civic, True))

    # Clue 2: Ford F150 in fifth house
    s.add(cars[4] == ford_f150)
    s.add(ford_house == 4)

    # Clue 3: Stir fry left of Eric
    s.add(stir_fry_house < eric_house)

    # Clue 4: May birthday left of Carol
    s.add(may_birthday_house < carol_house)

    # Clue 5: Very short left of April birthday
    s.add(very_short_house < april_birthday_house)

    # Clue 6: BMW not in third house
    s.add(cars[2] != bmw_3_series)

    # Clue 7: Two houses between stir fry and pizza
    s.add(Or(
        stir_fry_house + 3 == pizza_house,
        pizza_house + 3 == stir_fry_house
    ))

    # Clue 8: Soup directly left of Eric
    s.add(soup_house + 1 == eric_house)

    # Clue 9: Spaghetti and May birthday adjacent
    s.add(Or(
        spaghetti_house + 1 == may_birthday_house,
        may_birthday_house + 1 == spaghetti_house
    ))

    # Clue 10: Alice directly left of BMW
    s.add(alice_house + 1 == bmw_house)

    # Clue 11: Tesla left of tall
    s.add(tesla_house < tall_house)

    # Clue 12: Very tall owns Toyota Camry
    for i in range(6):
        s.add(If(heights[i] == very_tall, cars[i] == toyota_camry, True))
        s.add(If(cars[i] == toyota_camry, heights[i] == very_tall, True))

    # Clue 13: Peter directly left of pizza
    s.add(peter_house + 1 == pizza_house)

    # Clue 14: Stew not in third house
    s.add(foods[2] != stew)

    # Clue 15: One house between September birthday and very short
    s.add(Or(
        sept_birthday_house + 2 == very_short_house,
        very_short_house + 2 == sept_birthday_house
    ))

    # Clue 16: One house between March birthday and super tall
    s.add(Or(
        march_birthday_house + 2 == super_tall_house,
        super_tall_house + 2 == march_birthday_house
    ))

    # Clue 17: Tall is Bob
    for i in range(6):
        s.add(If(heights[i] == tall, names[i] == Bob, True))
        s.add(If(names[i] == Bob, heights[i] == tall, True))

    # Clue 18: May birthday right of Alice
    s.add(may_birthday_house > alice_house)

    # Clue 19: Very short in fourth house
    s.add(very_short_house == 3)
    s.add(heights[3] == very_short)

    # Clue 20: March birthday is short
    for i in range(6):
        s.add(If(birthdays[i] == mar, heights[i] == short, True))
        s.add(If(heights[i] == short, birthdays[i] == mar, True))

    # Clue 21: Carol owns Tesla
    for i in range(6):
        s.add(If(names[i] == Carol, cars[i] == tesla_model_3, True))
        s.add(If(cars[i] == tesla_model_3, names[i] == Carol, True))

    # Clue 22: Eric's birthday is January
    for i in range(6):
        s.add(If(names[i] == Eric, birthdays[i] == jan, True))
        s.add(If(birthdays[i] == jan, names[i] == Eric, True))

    # Check and get model
    if s.check() == sat:
        m = s.model()
        result = []
        attr_names = ['Name', 'Birthday', 'Food', 'Height', 'CarModel']
        for i in range(6):
            name_val = m.eval(names[i])
            birthday_val = m.eval(birthdays[i])
            food_val = m.eval(foods[i])
            height_val = m.eval(heights[i])
            car_val = m.eval(cars[i])
            row = [str(i+1)]
            for attr in [name_val, birthday_val, food_val, height_val, car_val]:
                row.append(str(attr))
            result.append(row)
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Birthday", "Food", "Height", "CarModel"],
                "rows": result
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()