from z3 import *
import json

def main():
    # Define the attribute lists
    names_att = ['Arnold','Bob','Peter','Alice','Carol','Eric']
    foods_att = ['stew','grilled cheese','stir fry','soup','pizza','spaghetti']
    heights_att = ['tall','average','super tall','very short','very tall','short']
    drinks_att = ['root beer','boba tea','coffee','water','tea','milk']
    pets_att = ['hamster','fish','cat','dog','bird','rabbit']
    phones_att = ['samsung galaxy s21','xiaomi mi 11','google pixel 6','iphone 13','huawei p50','oneplus 9']
    
    # Define the constants for the values by their index in the lists
    # Names
    ARNOLD = names_att.index('Arnold')
    BOB = names_att.index('Bob')
    PETER = names_att.index('Peter')
    ALICE = names_att.index('Alice')
    CAROL = names_att.index('Carol')
    ERIC = names_att.index('Eric')
    
    # Foods
    STEW = foods_att.index('stew')
    GRILLED_CHEESE = foods_att.index('grilled cheese')
    STIR_FRY = foods_att.index('stir fry')
    SOUP = foods_att.index('soup')
    PIZZA = foods_att.index('pizza')
    SPAGHETTI = foods_att.index('spaghetti')
    
    # Heights
    TALL = heights_att.index('tall')
    AVERAGE = heights_att.index('average')
    SUPER_TALL = heights_att.index('super tall')
    VERY_SHORT = heights_att.index('very short')
    VERY_TALL = heights_att.index('very tall')
    SHORT = heights_att.index('short')
    
    # Drinks
    ROOT_BEER = drinks_att.index('root beer')
    BOBA_TEA = drinks_att.index('boba tea')
    COFFEE = drinks_att.index('coffee')
    WATER = drinks_att.index('water')
    TEA = drinks_att.index('tea')
    MILK = drinks_att.index('milk')
    
    # Pets
    HAMSTER = pets_att.index('hamster')
    FISH = pets_att.index('fish')
    CAT = pets_att.index('cat')
    DOG = pets_att.index('dog')
    BIRD = pets_att.index('bird')
    RABBIT = pets_att.index('rabbit')
    
    # Phones
    SAMSUNG = phones_att.index('samsung galaxy s21')
    XIAOMI = phones_att.index('xiaomi mi 11')
    GOOGLE_PIXEL = phones_att.index('google pixel 6')
    IPHONE13 = phones_att.index('iphone 13')
    HUAWEI = phones_att.index('huawei p50')
    ONEPLUS = phones_att.index('oneplus 9')
    
    # Create Z3 integer variables for each attribute for the 6 houses
    names = IntVector('names', 6)
    foods = IntVector('foods', 6)
    heights = IntVector('heights', 6)
    drinks = IntVector('drinks', 6)
    pets = IntVector('pets', 6)
    phones = IntVector('phones', 6)
    
    s = Solver()
    
    # Each attribute must be between 0 and 5 (inclusive)
    for i in range(6):
        s.add(And(names[i] >= 0, names[i] < 6))
        s.add(And(foods[i] >= 0, foods[i] < 6))
        s.add(And(heights[i] >= 0, heights[i] < 6))
        s.add(And(drinks[i] >= 0, drinks[i] < 6))
        s.add(And(pets[i] >= 0, pets[i] < 6))
        s.add(And(phones[i] >= 0, phones[i] < 6))
    
    # Distinct constraints for each attribute
    s.add(Distinct(names))
    s.add(Distinct(foods))
    s.add(Distinct(heights))
    s.add(Distinct(drinks))
    s.add(Distinct(pets))
    s.add(Distinct(phones))
    
    # Clue 1: The person who uses an iPhone 13 is in the third house.
    s.add(phones[2] == IPHONE13)
    
    # Clue 2: Bob is the person who is tall.
    for i in range(6):
        s.add(If(names[i] == BOB, heights[i] == TALL, True))
    
    # Clue 3: The person who loves the soup is in the second house.
    s.add(foods[1] == SOUP)
    
    # Clue 4: The root beer lover is directly left of the person who uses a Xiaomi Mi 11.
    s.add(Or([And(drinks[i] == ROOT_BEER, phones[i+1] == XIAOMI) for i in range(5)]))
    
    # Clue 5: The person who uses a Huawei P50 is directly left of the person who loves eating grilled cheese.
    s.add(Or([And(phones[i] == HUAWEI, foods[i+1] == GRILLED_CHEESE) for i in range(5)]))
    
    # Clue 6: The person who loves stir fry is the person who likes milk.
    for i in range(6):
        s.add(If(foods[i] == STIR_FRY, drinks[i] == MILK, True))
    
    # Clue 7: The person who loves eating grilled cheese is the person who is tall.
    for i in range(6):
        s.add(If(foods[i] == GRILLED_CHEESE, heights[i] == TALL, True))
    
    # Clue 8: The person who uses a Xiaomi Mi 11 is the coffee drinker.
    for i in range(6):
        s.add(If(phones[i] == XIAOMI, drinks[i] == COFFEE, True))
    
    # Clue 9: The person who uses a OnePlus 9 is Arnold.
    for i in range(6):
        s.add(If(phones[i] == ONEPLUS, names[i] == ARNOLD, True))
    
    # Clue 10: The person who owns a rabbit is not in the fifth house.
    s.add(pets[4] != RABBIT)
    
    # Clue 11: The person with a pet hamster is somewhere to the right of the person who uses a Google Pixel 6.
    s.add(Or([ And(phones[i] == GOOGLE_PIXEL, Or([pets[j] == HAMSTER for j in range(i+1, 6)])) for i in range(5) ]))
    
    # Clue 12: The person who is super tall is the person with an aquarium of fish.
    for i in range(6):
        s.add(If(heights[i] == SUPER_TALL, pets[i] == FISH, True))
    
    # Clue 13: The person with an aquarium of fish is Alice.
    for i in range(6):
        s.add(If(pets[i] == FISH, names[i] == ALICE, True))
    
    # Clue 14: The tea drinker is directly left of the person who is a pizza lover.
    s.add(Or([And(drinks[i] == TEA, foods[i+1] == PIZZA) for i in range(5)]))
    
    # Clue 15: The person who uses a Samsung Galaxy S21 is Carol.
    for i in range(6):
        s.add(If(phones[i] == SAMSUNG, names[i] == CAROL, True))
    
    # Clue 16: The person who is a pizza lover is the person who is short.
    for i in range(6):
        s.add(If(foods[i] == PIZZA, heights[i] == SHORT, True))
    
    # Clue 17: Arnold is the person who is very tall.
    for i in range(6):
        s.add(If(names[i] == ARNOLD, heights[i] == VERY_TALL, True))
    
    # Clue 18: The person who loves the spaghetti eater is the person who uses a Google Pixel 6.
    for i in range(6):
        s.add(If(foods[i] == SPAGHETTI, phones[i] == GOOGLE_PIXEL, True))
    
    # Clue 19: The boba tea drinker is somewhere to the right of the person who loves the soup.
    s.add(Or([drinks[i] == BOBA_TEA for i in range(2,6)]))
    
    # Clue 20: The person with a pet hamster is not in the fifth house.
    s.add(pets[4] != HAMSTER)
    
    # Clue 21: The person who is very tall is not in the second house.
    s.add(heights[1] != VERY_TALL)
    
    # Clue 22: The person who is super tall is somewhere to the left of Peter.
    s.add(Or([ And(heights[i] == SUPER_TALL, names[j] == PETER, i < j) for i in range(6) for j in range(6) if i < j ]))
    
    # Clue 23: The person who is very short is the person who loves the spaghetti eater.
    for i in range(6):
        s.add(If(heights[i] == VERY_SHORT, foods[i] == SPAGHETTI, True))
    
    # Clue 24: The person who keeps a pet bird is somewhere to the left of the person who loves the spaghetti eater.
    s.add(Or([ And(pets[i] == BIRD, foods[j] == SPAGHETTI, i < j) for i in range(6) for j in range(6) if i < j ]))
    
    # Clue 25: The person with an aquarium of fish is directly left of Eric.
    s.add(Or([And(pets[i] == FISH, names[i+1] == ERIC) for i in range(5)]))
    
    # Clue 26: The person who owns a dog is the person who likes milk.
    for i in range(6):
        s.add(If(pets[i] == DOG, drinks[i] == MILK, True))
    
    if s.check() == sat:
        m = s.model()
        table = []
        for i in range(6):
            house_num = str(i+1)
            n_val = m[names[i]].as_long()
            name_str = names_att[n_val]
            f_val = m[foods[i]].as_long()
            food_str = foods_att[f_val]
            h_val = m[heights[i]].as_long()
            height_str = heights_att[h_val]
            d_val = m[drinks[i]].as_long()
            drink_str = drinks_att[d_val]
            p_val = m[pets[i]].as_long()
            pet_str = pets_att[p_val]
            ph_val = m[phones[i]].as_long()
            phone_str = phones_att[ph_val]
            table.append([house_num, name_str, food_str, height_str, drink_str, pet_str, phone_str])
        
        result = {
            "solution": {
                "header": ["House", "Name", "Food", "Height", "Drink", "Pet", "PhoneModel"],
                "rows": table
            }
        }
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == '__main__':
    main()