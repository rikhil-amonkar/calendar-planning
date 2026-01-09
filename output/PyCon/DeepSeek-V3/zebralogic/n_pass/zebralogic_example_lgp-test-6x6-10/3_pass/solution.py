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
        problem.addConstraint(lambda name, height, h=house: (name == "Bob") == (height == "tall"), 
                            [f"name_{house}", f"height_{house}"])
    
    # Clue 3: The person who loves the soup is in the second house.
    problem.addConstraint(lambda food: food == "soup", ["food_2"])
    
    # Clue 4: The root beer lover is directly left of the person who uses a Xiaomi Mi 11.
    for i in range(1, 6):
        problem.addConstraint(lambda drink, phone, idx=i: (drink == "root beer") == (phone == "xiaomi mi 11"), 
                            [f"drink_{i}", f"phone_{i+1}"])
    
    # Clue 5: The person who uses a Huawei P50 is directly left of the person who loves eating grilled cheese.
    for i in range(1, 6):
        problem.addConstraint(lambda phone, food, idx=i: (phone == "huawei p50") == (food == "grilled cheese"), 
                            [f"phone_{i}", f"food_{i+1}"])
    
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
    # This means the hamster owner must be in a higher numbered house than the Pixel 6 user
    for i in range(1, 7):
        for j in range(1, 7):
            if i >= j:  # hamster house not strictly right of pixel house
                problem.addConstraint(lambda pet_i, phone_j, h_i=i, h_j=j: 
                                    not (pet_i == "hamster" and phone_j == "google pixel 6"), 
                                    [f"pet_{i}", f"phone_{j}"])
    
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
        problem.addConstraint(lambda drink, food, idx=i: (drink == "tea") == (food == "pizza"), 
                            [f"drink_{i}", f"food_{i+1}"])
    
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