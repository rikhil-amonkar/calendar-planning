import json
from z3 import *

def main():
    # Create the solver
    s = Solver()

    # Define the attributes using EnumSort
    Name, (Eric, Peter, Arnold, Bob, Alice) = EnumSort('Name', ['Eric', 'Peter', 'Arnold', 'Bob', 'Alice'])
    HouseStyle, (modern, craftsman, ranch, victorian, colonial) = EnumSort('HouseStyle', ['modern', 'craftsman', 'ranch', 'victorian', 'colonial'])
    Mother, (Penny, Kailyn, Holly, Janelle, Aniya) = EnumSort('Mother', ['Penny', 'Kailyn', 'Holly', 'Janelle', 'Aniya'])
    PhoneModel, (oneplus9, google_pixel6, huawei_p50, iphone13, samsung_galaxy_s21) = EnumSort('PhoneModel', ['oneplus9', 'google_pixel6', 'huawei_p50', 'iphone13', 'samsung_galaxy_s21'])
    Drink, (coffee, water, root_beer, tea, milk) = EnumSort('Drink', ['coffee', 'water', 'root_beer', 'tea', 'milk'])
    Animal, (fish, dog, horse, bird, cat) = EnumSort('Animal', ['fish', 'dog', 'horse', 'bird', 'cat'])

    # Create variables for each house
    houses = []
    for i in range(5):
        name = Const(f'name_{i}', Name)
        style = Const(f'style_{i}', HouseStyle)
        mother = Const(f'mother_{i}', Mother)
        phone = Const(f'phone_{i}', PhoneModel)
        drink = Const(f'drink_{i}', Drink)
        animal = Const(f'animal_{i}', Animal)
        houses.append((name, style, mother, phone, drink, animal))

    # Each attribute must be unique
    s.add(Distinct([name for name, _, _, _, _, _ in houses]))
    s.add(Distinct([style for _, style, _, _, _, _ in houses]))
    s.add(Distinct([mother for _, _, mother, _, _, _ in houses]))
    s.add(Distinct([phone for _, _, _, phone, _, _ in houses]))
    s.add(Distinct([drink for _, _, _, _, drink, _ in houses]))
    s.add(Distinct([animal for _, _, _, _, _, animal in houses]))

    # Clue 1: The person who uses a Google Pixel 6 is not in the first house.
    s.add(Not(houses[0][3] == google_pixel6))

    # Clue 2: The one who only drinks water is Alice.
    for i in range(5):
        s.add(Implies(houses[i][4] == water, houses[i][0] == Alice))

    # Clue 3: The person living in a colonial-style house is somewhere to the right of the person who uses a Huawei P50.
    for i in range(5):
        for j in range(5):
            if i > j:
                s.add(Implies(And(houses[i][1] == colonial, houses[j][3] == huawei_p50), True))
            else:
                s.add(Not(And(houses[i][1] == colonial, houses[j][3] == huawei_p50)))

    # Clue 4: The person who keeps horses is the person who uses a OnePlus 9.
    for i in range(5):
        s.add(Implies(houses[i][5] == horse, houses[i][3] == oneplus9))
        s.add(Implies(houses[i][3] == oneplus9, houses[i][5] == horse))

    # Clue 5: The person in a ranch-style home is the person whose mother's name is Kailyn.
    for i in range(5):
        s.add(Implies(houses[i][1] == ranch, houses[i][2] == Kailyn))
        s.add(Implies(houses[i][2] == Kailyn, houses[i][1] == ranch))

    # Clue 6: The root beer lover is the cat lover.
    for i in range(5):
        s.add(Implies(houses[i][4] == root_beer, houses[i][5] == cat))
        s.add(Implies(houses[i][5] == cat, houses[i][4] == root_beer))

    # Clue 7: The person living in a colonial-style house is not in the fourth house.
    s.add(Not(houses[3][1] == colonial))

    # Clue 8: The bird keeper is in the fourth house.
    s.add(houses[3][5] == bird)

    # Clue 9: The tea drinker is Bob.
    for i in range(5):
        s.add(Implies(houses[i][4] == tea, houses[i][0] == Bob))

    # Clue 10: The tea drinker is somewhere to the right of the person whose mother's name is Kailyn.
    for i in range(5):
        for j in range(5):
            if i > j:
                s.add(Implies(And(houses[i][4] == tea, houses[j][2] == Kailyn), True))
            else:
                s.add(Not(And(houses[i][4] == tea, houses[j][2] == Kailyn)))

    # Clue 11: The root beer lover is somewhere to the left of the person whose mother's name is Kailyn.
    for i in range(5):
        for j in range(5):
            if i < j:
                s.add(Implies(And(houses[i][4] == root_beer, houses[j][2] == Kailyn), True))
            else:
                s.add(Not(And(houses[i][4] == root_beer, houses[j][2] == Kailyn)))

    # Clue 12: The person who keeps horses is the person in a modern-style house.
    for i in range(5):
        s.add(Implies(houses[i][5] == horse, houses[i][1] == modern))
        s.add(Implies(houses[i][1] == modern, houses[i][5] == horse))

    # Clue 13: The person who uses an iPhone 13 is the person who likes milk.
    for i in range(5):
        s.add(Implies(houses[i][3] == iphone13, houses[i][4] == milk))
        s.add(Implies(houses[i][4] == milk, houses[i][3] == iphone13))

    # Clue 14: The dog owner is the person who likes milk.
    for i in range(5):
        s.add(Implies(houses[i][5] == dog, houses[i][4] == milk))
        s.add(Implies(houses[i][4] == milk, houses[i][5] == dog))

    # Clue 15: The person who uses a Google Pixel 6 is the person in a Craftsman-style house.
    for i in range(5):
        s.add(Implies(houses[i][3] == google_pixel6, houses[i][1] == craftsman))
        s.add(Implies(houses[i][1] == craftsman, houses[i][3] == google_pixel6))

    # Clue 16: Eric is not in the second house.
    s.add(Not(houses[1][0] == Eric))

    # Clue 17: The tea drinker is in the fourth house.
    s.add(houses[3][4] == tea)

    # Clue 18: The person who keeps horses is in the third house.
    s.add(houses[2][5] == horse)

    # Clue 19: The person in a modern-style house is the person whose mother's name is Penny.
    for i in range(5):
        s.add(Implies(houses[i][1] == modern, houses[i][2] == Penny))
        s.add(Implies(houses[i][2] == Penny, houses[i][1] == modern))

    # Clue 20: The root beer lover is Peter.
    for i in range(5):
        s.add(Implies(houses[i][4] == root_beer, houses[i][0] == Peter))

    # Clue 21: The person whose mother's name is Aniya is not in the fourth house.
    s.add(Not(houses[3][2] == Aniya))

    # Clue 22: The person whose mother's name is Janelle is the one who only drinks water.
    for i in range(5):
        s.add(Implies(houses[i][2] == Janelle, houses[i][4] == water))
        s.add(Implies(houses[i][4] == water, houses[i][2] == Janelle))

    # Check for solution
    if s.check() == sat:
        model = s.model()
        
        # Mapping from enum values to original strings
        name_map = { Eric: "Eric", Peter: "Peter", Arnold: "Arnold", Bob: "Bob", Alice: "Alice" }
        style_map = { modern: "modern", craftsman: "craftsman", ranch: "ranch", victorian: "victorian", colonial: "colonial" }
        mother_map = { Penny: "Penny", Kailyn: "Kailyn", Holly: "Holly", Janelle: "Janelle", Aniya: "Aniya" }
        phone_map = { oneplus9: "oneplus 9", google_pixel6: "google pixel 6", huawei_p50: "huawei p50", iphone13: "iphone 13", samsung_galaxy_s21: "samsung galaxy s21" }
        drink_map = { coffee: "coffee", water: "water", root_beer: "root beer", tea: "tea", milk: "milk" }
        animal_map = { fish: "fish", dog: "dog", horse: "horse", bird: "bird", cat: "cat" }
        
        # Prepare the solution rows
        rows = []
        for i in range(5):
            name_val = model.evaluate(houses[i][0])
            style_val = model.evaluate(houses[i][1])
            mother_val = model.evaluate(houses[i][2])
            phone_val = model.evaluate(houses[i][3])
            drink_val = model.evaluate(houses[i][4])
            animal_val = model.evaluate(houses[i][5])
            
            row = [
                str(i+1),
                name_map[name_val],
                style_map[style_val],
                mother_map[mother_val],
                phone_map[phone_val],
                drink_map[drink_val],
                animal_map[animal_val]
            ]
            rows.append(row)
        
        # Create the solution dictionary
        solution = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "Mother", "PhoneModel", "Drink", "Animal"],
                "rows": rows
            }
        }
        
        # Output as JSON
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()