import json
from z3 import *

def main():
    # Define EnumSorts for each attribute
    NameSort, (eric, peter, arnold, bob, alice) = EnumSort('Name', ['Eric', 'Peter', 'Arnold', 'Bob', 'Alice'])
    HouseStyleSort, (modern, craftsman, ranch, victorian, colonial) = EnumSort('HouseStyle', ['modern', 'craftsman', 'ranch', 'victorian', 'colonial'])
    MotherSort, (penny, kailyn, holly, janelle, aniya) = EnumSort('Mother', ['Penny', 'Kailyn', 'Holly', 'Janelle', 'Aniya'])
    PhoneSort, (oneplus9, google_pixel6, huawei_p50, iphone13, samsung_galaxy_s21) = EnumSort('Phone', ['oneplus 9', 'google pixel 6', 'huawei p50', 'iphone 13', 'samsung galaxy s21'])
    DrinkSort, (coffee, water, root_beer, tea, milk) = EnumSort('Drink', ['coffee', 'water', 'root beer', 'tea', 'milk'])
    AnimalSort, (fish, dog, horse, bird, cat) = EnumSort('Animal', ['fish', 'dog', 'horse', 'bird', 'cat'])

    # Create dictionaries to map Z3 constants to strings
    name_dict = { eric: 'Eric', peter: 'Peter', arnold: 'Arnold', bob: 'Bob', alice: 'Alice' }
    style_dict = { modern: 'modern', craftsman: 'craftsman', ranch: 'ranch', victorian: 'victorian', colonial: 'colonial' }
    mother_dict = { penny: 'Penny', kailyn: 'Kailyn', holly: 'Holly', janelle: 'Janelle', aniya: 'Aniya' }
    phone_dict = { oneplus9: 'oneplus 9', google_pixel6: 'google pixel 6', huawei_p50: 'huawei p50', iphone13: 'iphone 13', samsung_galaxy_s21: 'samsung galaxy s21' }
    drink_dict = { coffee: 'coffee', water: 'water', root_beer: 'root beer', tea: 'tea', milk: 'milk' }
    animal_dict = { fish: 'fish', dog: 'dog', horse: 'horse', bird: 'bird', cat: 'cat' }

    # Create arrays for attributes for 5 houses (index 0 to 4 for house 1 to 5)
    names = [Const(f'name_{i}', NameSort) for i in range(5)]
    house_styles = [Const(f'style_{i}', HouseStyleSort) for i in range(5)]
    mothers = [Const(f'mother_{i}', MotherSort) for i in range(5)]
    phones = [Const(f'phone_{i}', PhoneSort) for i in range(5)]
    drinks = [Const(f'drink_{i}', DrinkSort) for i in range(5)]
    animals = [Const(f'animal_{i}', AnimalSort) for i in range(5)]

    s = Solver()

    # Distinct constraints for each attribute
    s.add(Distinct(names))
    s.add(Distinct(house_styles))
    s.add(Distinct(mothers))
    s.add(Distinct(phones))
    s.add(Distinct(drinks))
    s.add(Distinct(animals))

    # Fixed constraints from clues
    s.add(drinks[3] == tea)         # Clue 17: tea drinker in fourth house
    s.add(animals[3] == bird)        # Clue 8: bird keeper in fourth house
    s.add(animals[2] == horse)       # Clue 18: horse keeper in third house
    s.add(names[1] != eric)          # Clue 16: Eric not in second house
    s.add(mothers[3] != aniya)       # Clue 21: Aniya not in fourth house

    # Define colonial_style_index for clue 3 and 7
    colonial_style_index = Int('cs_idx')
    s.add(colonial_style_index >= 0, colonial_style_index <= 4)
    for i in range(5):
        s.add(If(house_styles[i] == colonial, colonial_style_index == i, True))
    s.add(colonial_style_index != 3) # Clue 7: colonial not in fourth house

    # Define huawei_phone_index for clue 3
    huawei_phone_index = Int('hw_idx')
    s.add(huawei_phone_index >= 0, huawei_phone_index <= 4)
    for i in range(5):
        s.add(If(phones[i] == huawei_p50, huawei_phone_index == i, True))

    # Define kailyn_mother_index for clues 10 and 11
    kailyn_mother_index = Int('kailyn_m_idx')
    s.add(kailyn_mother_index >= 0, kailyn_mother_index <= 4)
    for i in range(5):
        s.add(If(mothers[i] == kailyn, kailyn_mother_index == i, True))

    # Define rootbeer_drink_index for clue 11
    rootbeer_drink_index = Int('rootbeer_d_idx')
    s.add(rootbeer_drink_index >= 0, rootbeer_drink_index <= 4)
    for i in range(5):
        s.add(If(drinks[i] == root_beer, rootbeer_drink_index == i, True))

    # Relative constraints
    s.add(colonial_style_index > huawei_phone_index)      # Clue 3
    s.add(3 > kailyn_mother_index)                        # Clue 10
    s.add(rootbeer_drink_index < kailyn_mother_index)      # Clue 11

    # Other clues
    s.add(phones[0] != google_pixel6)                     # Clue 1
    for i in range(5):                                     # Clue 2
        s.add(If(drinks[i] == water, names[i] == alice, True))
    s.add(phones[2] == oneplus9)                          # Clue 4
    for i in range(5):                                     # Clue 5
        s.add(If(house_styles[i] == ranch, mothers[i] == kailyn, True))
    for i in range(5):                                     # Clue 6
        s.add(If(drinks[i] == root_beer, animals[i] == cat, True))
    s.add(names[3] == bob)                                # Clue 9
    s.add(house_styles[2] == modern)                      # Clue 12
    for i in range(5):                                     # Clue 13
        s.add(If(phones[i] == iphone13, drinks[i] == milk, True))
    for i in range(5):                                     # Clue 14
        s.add(If(animals[i] == dog, drinks[i] == milk, True))
    for i in range(5):                                     # Clue 15
        s.add(If(phones[i] == google_pixel6, house_styles[i] == craftsman, True))
    s.add(mothers[2] == penny)                            # Clue 19
    for i in range(5):                                     # Clue 20
        s.add(If(drinks[i] == root_beer, names[i] == peter, True))
    for i in range(5):                                     # Clue 22
        s.add(If(drinks[i] == water, mothers[i] == janelle, True))

    # Check and get model
    if s.check() == sat:
        m = s.model()
        rows = []
        for i in range(5):
            name_val = m.eval(names[i])
            style_val = m.eval(house_styles[i])
            mother_val = m.eval(mothers[i])
            phone_val = m.eval(phones[i])
            drink_val = m.eval(drinks[i])
            animal_val = m.eval(animals[i])
            
            name_str = name_dict[name_val]
            style_str = style_dict[style_val]
            mother_str = mother_dict[mother_val]
            phone_str = phone_dict[phone_val]
            drink_str = drink_dict[drink_val]
            animal_str = animal_dict[animal_val]
            
            rows.append([str(i+1), name_str, style_str, mother_str, phone_str, drink_str, animal_str])
        
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "Mother", "PhoneModel", "Drink", "Animal"],
                "rows": rows
            }
        }
        print(json.dumps(solution_dict))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()