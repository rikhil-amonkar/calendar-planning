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
    for house in houses:
        problem.addConstraint(lambda name, height: not (name == "Bob") or (height == "tall"), 
                            [f"name_{house}", f"height_{house}"])
        problem.addConstraint(lambda name, height: not (height == "tall") or (name == "Bob"), 
                            [f"name_{house}", f"height_{house}"])
    
    # Clue 3: The person who loves the soup is in the second house.
    problem.addConstraint(lambda food: food == "soup", ["food_2"])
    
    # Clue 4: The root beer lover is directly left of the person who uses a Xiaomi Mi 11.
    for i in range(1, 6):
        problem.addConstraint(lambda drink_i, phone_i1: not (drink_i == "root beer") or (phone_i1 == "xiaomi mi 11"), 
                            [f"drink_{i}", f"phone_{i+1}"])
    # Ensure only one root beer drinker is left of Xiaomi
    problem.addConstraint(lambda d1,d2,d3,d4,d5,d6,p1,p2,p3,p4,p5,p6: 
                         sum(1 for i in range(6) if [d1,d2,d3,d4,d5,d6][i] == "root beer" and [p1,p2,p3,p4,p5,p6][min(i+1,5)] == "xiaomi mi 11") == 1,
                         [f"drink_{h}" for h in houses] + [f"phone_{h}" for h in houses])
    
    # Clue 5: The person who uses a Huawei P50 is directly left of the person who loves eating grilled cheese.
    for i in range(1, 6):
        problem.addConstraint(lambda phone_i, food_i1: not (phone_i == "huawei p50") or (food_i1 == "grilled cheese"), 
                            [f"phone_{i}", f"food_{i+1}"])
    # Ensure only one Huawei is left of grilled cheese
    problem.addConstraint(lambda p1,p2,p3,p4,p5,p6,f1,f2,f3,f4,f5,f6: 
                         sum(1 for i in range(6) if [p1,p2,p3,p4,p5,p6][i] == "huawei p50" and [f1,f2,f3,f4,f5,f6][min(i+1,5)] == "grilled cheese") == 1,
                         [f"phone_{h}" for h in houses] + [f"food_{h}" for h in houses])
    
    # Clue 6: The person who loves stir fry is the person who likes milk.
    for house in houses:
        problem.addConstraint(lambda food, drink: (food == "stir fry") == (drink == "milk"), 
                            [f"food_{house}", f"drink_{house}"])
    
    # Clue 7: The person who loves eating grilled cheese is the person who is tall.
    for house in houses:
        problem.addConstraint(lambda food, height: (food == "grilled cheese") == (height == "tall"), 
                            [f"food_{house}", f"height_{house}"])
    
    # Clue 8: The person who uses a Xiaomi Mi 11 is the coffee drinker.
    for house in houses:
        problem.addConstraint(lambda phone, drink: (phone == "xiaomi mi 11") == (drink == "coffee"), 
                            [f"phone_{house}", f"drink_{house}"])
    
    # Clue 9: The person who uses a OnePlus 9 is Arnold.
    for house in houses:
        problem.addConstraint(lambda phone, name: (phone == "oneplus 9") == (name == "Arnold"), 
                            [f"phone_{house}", f"name_{house}"])
    
    # Clue 10: The person who owns a rabbit is not in the fifth house.
    problem.addConstraint(lambda pet: pet != "rabbit", ["pet_5"])
    
    # Clue 11: The person with a pet hamster is somewhere to the right of the person who uses a Google Pixel 6.
    def hamster_right_of_pixel(pets, phones):
        pixel_house = None
        hamster_house = None
        for i, (pet, phone) in enumerate(zip(pets, phones)):
            if phone == "google pixel 6":
                pixel_house = i
            if pet == "hamster":
                hamster_house = i
        return hamster_house is not None and pixel_house is not None and hamster_house > pixel_house
    
    problem.addConstraint(hamster_right_of_pixel, 
                         [f"pet_{h}" for h in houses] + [f"phone_{h}" for h in houses])
    
    # Clue 12: The person who is super tall is the person with an aquarium of fish.
    for house in houses:
        problem.addConstraint(lambda height, pet: (height == "super tall") == (pet == "fish"), 
                            [f"height_{house}", f"pet_{house}"])
    
    # Clue 13: The person with an aquarium of fish is Alice.
    for house in houses:
        problem.addConstraint(lambda pet, name: (pet == "fish") == (name == "Alice"), 
                            [f"pet_{house}", f"name_{house}"])
    
    # Clue 14: The tea drinker is directly left of the person who is a pizza lover.
    for i in range(1, 6):
        problem.addConstraint(lambda drink_i, food_i1: not (drink_i == "tea") or (food_i1 == "pizza"), 
                            [f"drink_{i}", f"food_{i+1}"])
    # Ensure only one tea drinker is left of pizza
    problem.addConstraint(lambda d1,d2,d3,d4,d5,d6,f1,f2,f3,f4,f5,f6: 
                         sum(1 for i in range(6) if [d1,d2,d3,d4,d5,d6][i] == "tea" and [f1,f2,f3,f4,f5,f6][min(i+1,5)] == "pizza") == 1,
                         [f"drink_{h}" for h in houses] + [f"food_{h}" for h in houses])
    
    # Clue 15: The person who uses a Samsung Galaxy S21 is Carol.
    for house in houses:
        problem.addConstraint(lambda phone, name: (phone == "samsung galaxy s21") == (name == "Carol"), 
                            [f"phone_{house}", f"name_{house}"])
    
    # Clue 16: The person who is a pizza lover is the person who is short.
    for house in houses:
        problem.addConstraint(lambda food, height: (food == "pizza") == (height == "short"), 
                            [f"food_{house}", f"height_{house}"])
    
    # Clue 17: Arnold is the person who is very tall.
    for house in houses:
        problem.addConstraint(lambda name, height: (name == "Arnold") == (height == "very tall"), 
                            [f"name_{house}", f"height_{house}"])
    
    # Clue 18: The person who loves the spaghetti eater is the person who uses a Google Pixel 6.
    for house in houses:
        problem.addConstraint(lambda food, phone: (food == "spaghetti") == (phone == "google pixel 6"), 
                            [f"food_{house}", f"phone_{house}"])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if solutions:
        # Convert to the required format
        result = []
        for house in houses:
            solution = solutions[0]  # Take first solution
            house_data = {
                "house": house,
                "name": solution[f"name_{house}"],
                "food": solution[f"food_{house}"],
                "height": solution[f"height_{house}"],
                "drink": solution[f"drink_{house}"],
                "pet": solution[f"pet_{house}"],
                "phone": solution[f"phone_{house}"]
            }
            result.append(house_data)
        
        return result
    else:
        return None

# Execute and print result
if __name__ == "__main__":
    solution = solve_puzzle()
    if solution:
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")