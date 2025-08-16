from z3 import *
import json

def main():
    s = Solver()
    N = 6

    # Create Z3 Int variables for each attribute in each house (houses indexed 0..5)
    names  = [Int(f"name_{i}") for i in range(N)]
    foods  = [Int(f"food_{i}") for i in range(N)]
    heights = [Int(f"height_{i}") for i in range(N)]
    drinks = [Int(f"drink_{i}") for i in range(N)]
    pets   = [Int(f"pet_{i}") for i in range(N)]
    phones = [Int(f"phone_{i}") for i in range(N)]
    
    # Each variable is in the domain 0 .. 5.
    for var in names + foods + heights + drinks + pets + phones:
        s.add(var >= 0, var < N)
    
    # All attributes in each category are all different.
    s.add(Distinct(names))
    s.add(Distinct(foods))
    s.add(Distinct(heights))
    s.add(Distinct(drinks))
    s.add(Distinct(pets))
    s.add(Distinct(phones))
    
    # Mapping of our codes:
    # Names: 0: Arnold, 1: Bob, 2: Peter, 3: Alice, 4: Carol, 5: Eric
    # Foods: 0: stew, 1: grilled cheese, 2: stir fry, 3: soup, 4: pizza, 5: spaghetti
    # Heights: 0: tall, 1: average, 2: super tall, 3: very short, 4: very tall, 5: short
    # Drinks: 0: root beer, 1: boba tea, 2: coffee, 3: water, 4: tea, 5: milk
    # Pets: 0: hamster, 1: fish, 2: cat, 3: dog, 4: bird, 5: rabbit
    # Phones: 0: samsung galaxy s21, 1: xiaomi mi 11, 2: google pixel 6, 3: iphone 13, 4: huawei p50, 5: oneplus 9

    # Clue 1: The person who uses an iPhone 13 is in the third house.
    s.add(phones[2] == 3)
    
    # Clue 2: Bob is the person who is tall.
    for i in range(N):
        s.add(Implies(names[i] == 1, heights[i] == 0))
    
    # Clue 3: The person who loves the soup is in the second house.
    s.add(foods[1] == 3)
    
    # Clue 4: The root beer lover is directly left of the person who uses a Xiaomi Mi 11.
    for i in range(N - 1):
        s.add(Implies(drinks[i] == 0, phones[i+1] == 1))
    for i in range(1, N):
        s.add(Implies(phones[i] == 1, drinks[i-1] == 0))
    
    # Clue 5: The person who uses a Huawei P50 is directly left of the person who loves eating grilled cheese.
    for i in range(N - 1):
        s.add(Implies(phones[i] == 4, foods[i+1] == 1))
    for i in range(1, N):
        s.add(Implies(foods[i] == 1, phones[i-1] == 4))
    
    # Clue 6: The person who loves stir fry is the person who likes milk.
    for i in range(N):
        s.add((foods[i] == 2) == (drinks[i] == 5))
    
    # Clue 7: The person who loves eating grilled cheese is the person who is tall.
    for i in range(N):
        s.add((foods[i] == 1) == (heights[i] == 0))
    
    # Clue 8: The person who uses a Xiaomi Mi 11 is the coffee drinker.
    for i in range(N):
        s.add((phones[i] == 1) == (drinks[i] == 2))
    
    # Clue 9: The person who uses a OnePlus 9 is Arnold.
    for i in range(N):
        s.add((phones[i] == 5) == (names[i] == 0))
    
    # Clue 10: The person who owns a rabbit is not in the fifth house.
    s.add(pets[4] != 5)
    
    # Clue 11: The person with a pet hamster is somewhere to the right of the person who uses a Google Pixel 6.
    for i in range(N):
        for j in range(N):
            s.add(Implies(And(phones[i] == 2, pets[j] == 0), j > i))
    
    # Clue 12: The person who is super tall is the person with an aquarium of fish.
    for i in range(N):
        s.add((heights[i] == 2) == (pets[i] == 1))
    
    # Clue 13: The person with an aquarium of fish is Alice.
    for i in range(N):
        s.add((pets[i] == 1) == (names[i] == 3))
    
    # Clue 14: The tea drinker is directly left of the person who is a pizza lover.
    for i in range(N - 1):
        s.add(Implies(drinks[i] == 4, foods[i+1] == 4))
    for i in range(1, N):
        s.add(Implies(foods[i] == 4, drinks[i-1] == 4))
    
    # Clue 15: The person who uses a Samsung Galaxy S21 is Carol.
    for i in range(N):
        s.add((phones[i] == 0) == (names[i] == 4))
    
    # Clue 16: The person who is a pizza lover is the person who is short.
    for i in range(N):
        s.add((foods[i] == 4) == (heights[i] == 5))
    
    # Clue 17: Arnold is the person who is very tall.
    for i in range(N):
        s.add((names[i] == 0) == (heights[i] == 4))
    
    # Clue 18: The person who loves the spaghetti is the person who uses a Google Pixel 6.
    for i in range(N):
        s.add((foods[i] == 5) == (phones[i] == 2))
    
    # Clue 19: The boba tea drinker is somewhere to the right of the person who loves the soup.
    # Since the soup‐lover is in house 2 (index 1), boba tea cannot be in house 1 or earlier.
    s.add(drinks[0] != 1)
    s.add(drinks[1] != 1)
    
    # Clue 20: The person with a pet hamster is not in the fifth house.
    s.add(pets[4] != 0)
    
    # Clue 21: The person who is very tall is not in the second house.
    s.add(heights[1] != 4)
    
    # Clue 22: The person who is super tall is somewhere to the left of Peter.
    for i in range(N):
        for j in range(N):
            s.add(Implies(And(heights[i] == 2, names[j] == 2), i < j))
    
    # Clue 23: The person who is very short is the person who loves the spaghetti.
    for i in range(N):
        s.add((heights[i] == 3) == (foods[i] == 5))
    
    # Clue 24: The person who keeps a pet bird is somewhere to the left of the person who loves the spaghetti.
    for i in range(N):
        for j in range(N):
            s.add(Implies(And(pets[i] == 4, foods[j] == 5), i < j))
    
    # Clue 25: The person with an aquarium of fish is directly left of Eric.
    # (And since the person with fish is Alice per Clue 13, Alice must be immediately left of Eric.)
    for i in range(N - 1):
        s.add(Implies(names[i] == 3, names[i+1] == 5))
    for i in range(1, N):
        s.add(Implies(names[i] == 5, names[i-1] == 3))
    
    # Clue 26: The person who owns a dog is the person who likes milk.
    for i in range(N):
        s.add((pets[i] == 3) == (drinks[i] == 5))
    
    if s.check() == sat:
        m = s.model()
        # Mapping lists for converting codes back into strings.
        names_list   = ["Arnold", "Bob", "Peter", "Alice", "Carol", "Eric"]
        foods_list   = ["stew", "grilled cheese", "stir fry", "soup", "pizza", "spaghetti"]
        heights_list = ["tall", "average", "super tall", "very short", "very tall", "short"]
        drinks_list  = ["root beer", "boba tea", "coffee", "water", "tea", "milk"]
        pets_list    = ["hamster", "fish", "cat", "dog", "bird", "rabbit"]
        phones_list  = ["samsung galaxy s21", "xiaomi mi 11", "google pixel 6", "iphone 13", "huawei p50", "oneplus 9"]
        
        solution_rows = []
        for i in range(N):
            solution_rows.append([
                str(i+1),
                names_list[m.evaluate(names[i]).as_long()],
                foods_list[m.evaluate(foods[i]).as_long()],
                heights_list[m.evaluate(heights[i]).as_long()],
                drinks_list[m.evaluate(drinks[i]).as_long()],
                pets_list[m.evaluate(pets[i]).as_long()],
                phones_list[m.evaluate(phones[i]).as_long()]
            ])
        result = {
            "solution": {
                "header": ["House", "Name", "Food", "Height", "Drink", "Pet", "PhoneModel"],
                "rows": solution_rows
            }
        }
        print(json.dumps(result, indent=2))
    else:
        print("No solution found.")

if __name__ == '__main__':
    main()