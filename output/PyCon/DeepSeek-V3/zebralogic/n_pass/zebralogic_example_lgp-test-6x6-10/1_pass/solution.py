import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each attribute
    houses = [1, 2, 3, 4, 5, 6]
    
    # All possible values for each attribute
    names = ["Arnold", "Bob", "Peter", "Alice", "Carol", "Eric"]
    foods = ["stew", "grilled cheese", "stir fry", "soup", "pizza", "spaghetti"]
    heights = ["tall", "average", "super tall", "very short", "very tall", "short"]
    drinks = ["root beer", "boba tea", "coffee", "water", "tea", "milk"]
    pets = ["hamster", "fish", "cat", "dog", "bird", "rabbit"]
    phones = ["samsung galaxy s21", "xiaomi mi 11", "google pixel 6", "iphone 13", "huawei p50", "oneplus 9"]
    
    # Add variables for each attribute per house
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"food_{house}", foods)
        problem.addVariable(f"height_{house}", heights)
        problem.addVariable(f"drink_{house}", drinks)
        problem.addVariable(f"pet_{house}", pets)
        problem.addVariable(f"phone_{house}", phones)
    
    # All attributes must be different
    problem.addConstraint(AllDifferentConstraint(), [f"name_{h}" for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"food_{h}" for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"height_{h}" for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"drink_{h}" for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"pet_{h}" for h in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"phone_{h}" for h in houses])
    
    # Clue 1: The person who uses an iPhone 13 is in the third house.
    problem.addConstraint(lambda phone: phone == "iphone 13", ["phone_3"])
    
    # Clue 2: Bob is the person who is tall.
    problem.addConstraint(lambda name, height: (name == "Bob") == (height == "tall"), 
                         ["name_1", "height_1"])
    problem.addConstraint(lambda name, height: (name == "Bob") == (height == "tall"), 
                         ["name_2", "height_2"])
    problem.addConstraint(lambda name, height: (name == "Bob") == (height == "tall"), 
                         ["name_3", "height_3"])
    problem.addConstraint(lambda name, height: (name == "Bob") == (height == "tall"), 
                         ["name_4", "height_4"])
    problem.addConstraint(lambda name, height: (name == "Bob") == (height == "tall"), 
                         ["name_5", "height_5"])
    problem.addConstraint(lambda name, height: (name == "Bob") == (height == "tall"), 
                         ["name_6", "height_6"])
    
    # Clue 3: The person who loves the soup is in the second house.
    problem.addConstraint(lambda food: food == "soup", ["food_2"])
    
    # Clue 4: The root beer lover is directly left of the person who uses a Xiaomi Mi 11.
    for i in range(1, 6):
        problem.addConstraint(lambda drink1, phone2: not(drink1 == "root beer" and phone2 == "xiaomi mi 11"), 
                             [f"drink_{i}", f"phone_{i+1}"])
    problem.addConstraint(lambda drink1, phone2: drink1 == "root beer" and phone2 == "xiaomi mi 11", 
                         ["drink_1", "phone_2"])
    problem.addConstraint(lambda drink2, phone3: drink2 == "root beer" and phone3 == "xiaomi mi 11", 
                         ["drink_2", "phone_3"])
    problem.addConstraint(lambda drink3, phone4: drink3 == "root beer" and phone4 == "xiaomi mi 11", 
                         ["drink_3", "phone_4"])
    problem.addConstraint(lambda drink4, phone5: drink4 == "root beer" and phone5 == "xiaomi mi 11", 
                         ["drink_4", "phone_5"])
    problem.addConstraint(lambda drink5, phone6: drink5 == "root beer" and phone6 == "xiaomi mi 11", 
                         ["drink_5", "phone_6"])
    
    # Clue 5: The person who uses a Huawei P50 is directly left of the person who loves eating grilled cheese.
    for i in range(1, 6):
        problem.addConstraint(lambda phone1, food2: not(phone1 == "huawei p50" and food2 == "grilled cheese"), 
                             [f"phone_{i}", f"food_{i+1}"])
    problem.addConstraint(lambda phone1, food2: phone1 == "huawei p50" and food2 == "grilled cheese", 
                         ["phone_1", "food_2"])
    problem.addConstraint(lambda phone2, food3: phone2 == "huawei p50" and food3 == "grilled cheese", 
                         ["phone_2", "food_3"])
    problem.addConstraint(lambda phone3, food4: phone3 == "huawei p50" and food4 == "grilled cheese", 
                         ["phone_3", "food_4"])
    problem.addConstraint(lambda phone4, food5: phone4 == "huawei p50" and food5 == "grilled cheese", 
                         ["phone_4", "food_5"])
    problem.addConstraint(lambda phone5, food6: phone5 == "huawei p50" and food6 == "grilled cheese", 
                         ["phone_5", "food_6"])
    
    # Clue 6: The person who loves stir fry is the person who likes milk.
    problem.addConstraint(lambda food, drink: (food == "stir fry") == (drink == "milk"), 
                         ["food_1", "drink_1"])
    problem.addConstraint(lambda food, drink: (food == "stir fry") == (drink == "milk"), 
                         ["food_2", "drink_2"])
    problem.addConstraint(lambda food, drink: (food == "stir fry") == (drink == "milk"), 
                         ["food_3", "drink_3"])
    problem.addConstraint(lambda food, drink: (food == "stir fry") == (drink == "milk"), 
                         ["food_4", "drink_4"])
    problem.addConstraint(lambda food, drink: (food == "stir fry") == (drink == "milk"), 
                         ["food_5", "drink_5"])
    problem.addConstraint(lambda food, drink: (food == "stir fry") == (drink == "milk"), 
                         ["food_6", "drink_6"])
    
    # Clue 7: The person who loves eating grilled cheese is the person who is tall.
    problem.addConstraint(lambda food, height: (food == "grilled cheese") == (height == "tall"), 
                         ["food_1", "height_1"])
    problem.addConstraint(lambda food, height: (food == "grilled cheese") == (height == "tall"), 
                         ["food_2", "height_2"])
    problem.addConstraint(lambda food, height: (food == "grilled cheese") == (height == "tall"), 
                         ["food_3", "height_3"])
    problem.addConstraint(lambda food, height: (food == "grilled cheese") == (height == "tall"), 
                         ["food_4", "height_4"])
    problem.addConstraint(lambda food, height: (food == "grilled cheese") == (height == "tall"), 
                         ["food_5", "height_5"])
    problem.addConstraint(lambda food, height: (food == "grilled cheese") == (height == "tall"), 
                         ["food_6", "height_6"])
    
    # Clue 8: The person who uses a Xiaomi Mi 11 is the coffee drinker.
    problem.addConstraint(lambda phone, drink: (phone == "xiaomi mi 11") == (drink == "coffee"), 
                         ["phone_1", "drink_1"])
    problem.addConstraint(lambda phone, drink: (phone == "xiaomi mi 11") == (drink == "coffee"), 
                         ["phone_2", "drink_2"])
    problem.addConstraint(lambda phone, drink: (phone == "xiaomi mi 11") == (drink == "coffee"), 
                         ["phone_3", "drink_3"])
    problem.addConstraint(lambda phone, drink: (phone == "xiaomi mi 11") == (drink == "coffee"), 
                         ["phone_4", "drink_4"])
    problem.addConstraint(lambda phone, drink: (phone == "xiaomi mi 11") == (drink == "coffee"), 
                         ["phone_5", "drink_5"])
    problem.addConstraint(lambda phone, drink: (phone == "xiaomi mi 11") == (drink == "coffee"), 
                         ["phone_6", "drink_6"])
    
    # Clue 9: The person who uses a OnePlus 9 is Arnold.
    problem.addConstraint(lambda phone, name: (phone == "oneplus 9") == (name == "Arnold"), 
                         ["phone_1", "name_1"])
    problem.addConstraint(lambda phone, name: (phone == "oneplus 9") == (name == "Arnold"), 
                         ["phone_2", "name_2"])
    problem.addConstraint(lambda phone, name: (phone == "oneplus 9") == (name == "Arnold"), 
                         ["phone_3", "name_3"])
    problem.addConstraint(lambda phone, name: (phone == "oneplus 9") == (name == "Arnold"), 
                         ["phone_4", "name_4"])
    problem.addConstraint(lambda phone, name: (phone == "oneplus 9") == (name == "Arnold"), 
                         ["phone_5", "name_5"])
    problem.addConstraint(lambda phone, name: (phone == "oneplus 9") == (name == "Arnold"), 
                         ["phone_6", "name_6"])
    
    # Clue 10: The person who owns a rabbit is not in the fifth house.
    problem.addConstraint(lambda pet: pet != "rabbit", ["pet_5"])
    
    # Clue 11: The person with a pet hamster is somewhere to the right of the person who uses a Google Pixel 6.
    def hamster_right_of_pixel(hamster_house, pixel_house):
        if hamster_house == "hamster" and pixel_house == "google pixel 6":
            return False
        return True
    
    for i in range(1, 7):
        for j in range(i, 7):
            problem.addConstraint(hamster_right_of_pixel, [f"pet_{i}", f"phone_{j}"])
    
    # Clue 12: The person who is super tall is the person with an aquarium of fish.
    problem.addConstraint(lambda height, pet: (height == "super tall") == (pet == "fish"), 
                         ["height_1", "pet_1"])
    problem.addConstraint(lambda height, pet: (height == "super tall") == (pet == "fish"), 
                         ["height_2", "pet_2"])
    problem.addConstraint(lambda height, pet: (height == "super tall") == (pet == "fish"), 
                         ["height_3", "pet_3"])
    problem.addConstraint(lambda height, pet: (height == "super tall") == (pet == "fish"), 
                         ["height_4", "pet_4"])
    problem.addConstraint(lambda height, pet: (height == "super tall") == (pet == "fish"), 
                         ["height_5", "pet_5"])
    problem.addConstraint(lambda height, pet: (height == "super tall") == (pet == "fish"), 
                         ["height_6", "pet_6"])
    
    # Clue 13: The person with an aquarium of fish is Alice.
    problem.addConstraint(lambda pet, name: (pet == "fish") == (name == "Alice"), 
                         ["pet_1", "name_1"])
    problem.addConstraint(lambda pet, name: (pet == "fish") == (name == "Alice"), 
                         ["pet_2", "name_2"])
    problem.addConstraint(lambda pet, name: (pet == "fish") == (name == "Alice"), 
                         ["pet_3", "name_3"])
    problem.addConstraint(lambda pet, name: (pet == "fish") == (name == "Alice"), 
                         ["pet_4", "name_4"])
    problem.addConstraint(lambda pet, name: (pet == "fish") == (name == "Alice"), 
                         ["pet_5", "name_5"])
    problem.addConstraint(lambda pet, name: (pet == "fish") == (name == "Alice"), 
                         ["pet_6", "name_6"])
    
    # Clue 14: The tea drinker is directly left of the person who is a pizza lover.
    for i in range(1, 6):
        problem.addConstraint(lambda drink1, food2: not(drink1 == "tea" and food2 == "pizza"), 
                             [f"drink_{i}", f"food_{i+1}"])
    problem.addConstraint(lambda drink1, food2: drink1 == "tea" and food2 == "pizza", 
                         ["drink_1", "food_2"])
    problem.addConstraint(lambda drink2, food3: drink2 == "tea" and food3 == "pizza", 
                         ["drink_2", "food_3"])
    problem.addConstraint(lambda drink3, food4: drink3 == "tea" and food4 == "pizza", 
                         ["drink_3", "food_4"])
    problem.addConstraint(lambda drink4, food5: drink4 == "tea" and food5 == "pizza", 
                         ["drink_4", "food_5"])
    problem.addConstraint(lambda drink5, food6: drink5 == "tea" and food6 == "pizza", 
                         ["drink_5", "food_6"])
    
    # Clue 15: The person who uses a Samsung Galaxy S21 is Carol.
    problem.addConstraint(lambda phone, name: (phone == "samsung galaxy s21") == (name == "Carol"), 
                         ["phone_1", "name_1"])
    problem.addConstraint(lambda phone, name: (phone == "samsung galaxy s21") == (name == "Carol"), 
                         ["phone_2", "name_2"])
    problem.addConstraint(lambda phone, name: (phone == "samsung galaxy s21") == (name == "Carol"), 
                         ["phone_3", "name_3"])
    problem.addConstraint(lambda phone, name: (phone == "samsung galaxy s21") == (name == "Carol"), 
                         ["phone_4", "name_4"])
    problem.addConstraint(lambda phone, name: (phone == "samsung galaxy s21") == (name == "Carol"), 
                         ["phone_5", "name_5"])
    problem.addConstraint(lambda phone, name: (phone == "samsung galaxy s21") == (name == "Carol"), 
                         ["phone_6", "name_6"])
    
    # Clue 16: The person who is a pizza lover is the person who is short.
    problem.addConstraint(lambda food, height: (food == "pizza") == (height == "short"), 
                         ["food_1", "height_1"])
    problem.addConstraint(lambda food, height: (food == "pizza") == (height == "short"), 
                         ["food_2", "height_2"])
    problem.addConstraint(lambda food, height: (food == "pizza") == (height == "short"), 
                         ["food_3", "height_3"])
    problem.addConstraint(lambda food, height: (food == "pizza") == (height == "short"), 
                         ["food_4", "height_4"])
    problem.addConstraint(lambda food, height: (food == "pizza") == (height == "short"), 
                         ["food_5", "height_5"])
    problem.addConstraint(lambda food, height: (food == "pizza") == (height == "short"), 
                         ["food_6", "height_6"])
    
    # Clue 17: Arnold is the person who is very tall.
    problem.addConstraint(lambda name, height: (name == "Arnold") == (height == "very tall"), 
                         ["name_1", "height_1"])
    problem.addConstraint(lambda name, height: (name == "Arnold") == (height == "very tall"), 
                         ["name_2", "height_2"])
    problem.addConstraint(lambda name, height: (name == "Arnold") == (height == "very tall"), 
                         ["name_3", "height_3"])
    problem.addConstraint(lambda name, height: (name == "Arnold") == (height == "very tall"), 
                         ["name_4", "height_4"])
    problem.addConstraint(lambda name, height: (name == "Arnold") == (height == "very tall"), 
                         ["name_5", "height_5"])
    problem.addConstraint(lambda name, height: (name == "Arnold") == (height == "very tall"), 
                         ["name_6", "height_6"])
    
    # Clue 18: The person who loves the spaghetti eater is the person who uses a Google Pixel 6.
    problem.addConstraint(lambda food, phone: (food == "spaghetti") == (phone == "google pixel 6"), 
                         ["food_1", "phone_1"])
    problem.addConstraint(lambda food, phone: (food == "spaghetti") == (phone == "google pixel 6"), 
                         ["food_2", "phone_2"])
    problem.addConstraint(lambda food, phone: (food == "spaghetti") == (phone == "google