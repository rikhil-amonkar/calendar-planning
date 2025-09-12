import json
from z3 import *

def main():
    s = Solver()
    
    # Define the attributes
    names = ['Arnold', 'Eric', 'Alice', 'Bob', 'Peter']
    vacations = ['mountain', 'city', 'cruise', 'beach', 'camping']
    educations = ['doctorate', 'high school', 'bachelor', 'associate', 'master']
    colors = ['blue', 'red', 'white', 'yellow', 'green']
    phones = ['google pixel 6', 'iphone 13', 'oneplus 9', 'huawei p50', 'samsung galaxy s21']
    foods = ['grilled cheese', 'stir fry', 'pizza', 'spaghetti', 'stew']
    
    # Create enums for each category
    Name = Datatype('Name')
    for n in names:
        Name.declare(n)
    Name = Name.create()
    
    Vacation = Datatype('Vacation')
    for v in vacations:
        Vacation.declare(v)
    Vacation = Vacation.create()
    
    Education = Datatype('Education')
    for e in educations:
        Education.declare(e)
    Education = Education.create()
    
    Color = Datatype('Color')
    for c in colors:
        Color.declare(c)
    Color = Color.create()
    
    Phone = Datatype('Phone')
    for p in phones:
        Phone.declare(p)
    Phone = Phone.create()
    
    Food = Datatype('Food')
    for f in foods:
        Food.declare(f)
    Food = Food.create()
    
    # Create variables for each house
    houses = [Int(f'house_{i}') for i in range(1,6)]
    name_vars = [Const(f'name_{i}', Name) for i in range(1,6)]
    vacation_vars = [Const(f'vacation_{i}', Vacation) for i in range(1,6)]
    education_vars = [Const(f'education_{i}', Education) for i in range(1,6)]
    color_vars = [Const(f'color_{i}', Color) for i in range(1,6)]
    phone_vars = [Const(f'phone_{i}', Phone) for i in range(1,6)]
    food_vars = [Const(f'food_{i}', Food) for i in range(1,6)]
    
    # Each attribute must be unique per category
    s.add(Distinct(name_vars))
    s.add(Distinct(vacation_vars))
    s.add(Distinct(education_vars))
    s.add(Distinct(color_vars))
    s.add(Distinct(phone_vars))
    s.add(Distinct(food_vars))
    
    # Add constraints from clues
    # Clue 1: The person who loves the stew is not in the first house.
    s.add(food_vars[0] != Food.stew)
    
    # Clue 2: There are two houses between the person who loves stir fry and the person with an associate's degree.
    for i in range(5):
        for j in range(5):
            if abs(i - j) == 3:  # Two houses between means |i-j| = 3
                s.add(Implies(food_vars[i] == Food.stir_fry, education_vars[j] == Education.associate))
                s.add(Implies(education_vars[j] == Education.associate, food_vars[i] == Food.stir_fry))
    
    # Clue 3: The person who enjoys mountain retreats is the person with a bachelor's degree.
    for i in range(5):
        s.add(Implies(vacation_vars[i] == Vacation.mountain, education_vars[i] == Education.bachelor))
        s.add(Implies(education_vars[i] == Education.bachelor, vacation_vars[i] == Vacation.mountain))
    
    # Clue 4: The person with a doctorate is somewhere to the right of Bob.
    bob_index = Int('bob_index')
    s.add(bob_index >= 1, bob_index <= 5)
    for i in range(5):
        s.add(Implies(name_vars[i] == Name.Bob, bob_index == i+1))
    doctorate_index = Int('doctorate_index')
    s.add(doctorate_index >= 1, doctorate_index <= 5)
    for i in range(5):
        s.add(Implies(education_vars[i] == Education.doctorate, doctorate_index == i+1))
    s.add(doctorate_index > bob_index)
    
    # Clue 5: The person who uses a Samsung Galaxy S21 is in the third house.
    s.add(phone_vars[2] == Phone.samsung_galaxy_s21)
    
    # Clue 6: Eric is the person with a doctorate.
    for i in range(5):
        s.add(Implies(name_vars[i] == Name.Eric, education_vars[i] == Education.doctorate))
        s.add(Implies(education_vars[i] == Education.doctorate, name_vars[i] == Name.Eric))
    
    # Clue 7: The person with a doctorate is in the third house.
    s.add(education_vars[2] == Education.doctorate)
    
    # Clue 8: The person who loves stir fry is the person with a bachelor's degree.
    for i in range(5):
        s.add(Implies(food_vars[i] == Food.stir_fry, education_vars[i] == Education.bachelor))
        s.add(Implies(education_vars[i] == Education.bachelor, food_vars[i] == Food.stir_fry))
    
    # Clue 9: The person with a doctorate is the person who is a pizza lover.
    for i in range(5):
        s.add(Implies(education_vars[i] == Education.doctorate, food_vars[i] == Food.pizza))
        s.add(Implies(food_vars[i] == Food.pizza, education_vars[i] == Education.doctorate))
    
    # Clue 10: The person whose favorite color is green is somewhere to the right of Peter.
    peter_index = Int('peter_index')
    s.add(peter_index >= 1, peter_index <= 5)
    for i in range(5):
        s.add(Implies(name_vars[i] == Name.Peter, peter_index == i+1))
    green_index = Int('green_index')
    s.add(green_index >= 1, green_index <= 5)
    for i in range(5):
        s.add(Implies(color_vars[i] == Color.green, green_index == i+1))
    s.add(green_index > peter_index)
    
    # Clue 11: The person who enjoys camping trips is the person who uses an iPhone 13.
    for i in range(5):
        s.add(Implies(vacation_vars[i] == Vacation.camping, phone_vars[i] == Phone.iphone_13))
        s.add(Implies(phone_vars[i] == Phone.iphone_13, vacation_vars[i] == Vacation.camping))
    
    # Clue 12: The person who likes going on cruises is Alice.
    for i in range(5):
        s.add(Implies(vacation_vars[i] == Vacation.cruise, name_vars[i] == Name.Alice))
        s.add(Implies(name_vars[i] == Name.Alice, vacation_vars[i] == Vacation.cruise))
    
    # Clue 13: There is one house between the person with a high school diploma and the person who uses a Samsung Galaxy S21.
    for i in range(5):
        for j in range(5):
            if abs(i - j) == 2:  # One house between means |i-j| = 2
                s.add(Implies(education_vars[i] == Education.high_school, phone_vars[j] == Phone.samsung_galaxy_s21))
                s.add(Implies(phone_vars[j] == Phone.samsung_galaxy_s21, education_vars[i] == Education.high_school))
    
    # Clue 14: The person who uses a Google Pixel 6 is Arnold.
    for i in range(5):
        s.add(Implies(phone_vars[i] == Phone.google_pixel_6, name_vars[i] == Name.Arnold))
        s.add(Implies(name_vars[i] == Name.Arnold, phone_vars[i] == Phone.google_pixel_6))
    
    # Clue 15: The person who uses a OnePlus 9 is somewhere to the right of the person who uses a Huawei P50.
    huawei_index = Int('huawei_index')
    s.add(huawei_index >= 1, huawei_index <= 5)
    for i in range(5):
        s.add(Implies(phone_vars[i] == Phone.huawei_p50, huawei_index == i+1))
    oneplus_index = Int('oneplus_index')
    s.add(oneplus_index >= 1, oneplus_index <= 5)
    for i in range(5):
        s.add(Implies(phone_vars[i] == Phone.oneplus_9, oneplus_index == i+1))
    s.add(oneplus_index > huawei_index)
    
    # Clue 16: Arnold is the person who loves eating grilled cheese.
    for i in range(5):
        s.add(Implies(name_vars[i] == Name.Arnold, food_vars[i] == Food.grilled_cheese))
        s.add(Implies(food_vars[i] == Food.grilled_cheese, name_vars[i] == Name.Arnold))
    
    # Clue 17: The person who loves eating grilled cheese is not in the fourth house.
    s.add(food_vars[3] != Food.grilled_cheese)
    
    # Clue 18: There are two houses between the person with a bachelor's degree and the person whose favorite color is red.
    for i in range(5):
        for j in range(5):
            if abs(i - j) == 3:  # Two houses between means |i-j| = 3
                s.add(Implies(education_vars[i] == Education.bachelor, color_vars[j] == Color.red))
                s.add(Implies(color_vars[j] == Color.red, education_vars[i] == Education.bachelor))
    
    # Clue 19: The person who loves beach vacations is somewhere to the right of the person who prefers city breaks.
    city_index = Int('city_index')
    s.add(city_index >= 1, city_index <= 5)
    for i in range(5):
        s.add(Implies(vacation_vars[i] == Vacation.city, city_index == i+1))
    beach_index = Int('beach_index')
    s.add(beach_index >= 1, beach_index <= 5)
    for i in range(5):
        s.add(Implies(vacation_vars[i] == Vacation.beach, beach_index == i+1))
    s.add(beach_index > city_index)
    
    # Clue 20: The person whose favorite color is green is not in the second house.
    s.add(color_vars[1] != Color.green)
    
    # Clue 21: The person who loves blue is somewhere to the right of Peter.
    blue_index = Int('blue_index')
    s.add(blue_index >= 1, blue_index <= 5)
    for i in range(5):
        s.add(Implies(color_vars[i] == Color.blue, blue_index == i+1))
    s.add(blue_index > peter_index)
    
    # Clue 22: There is one house between the person who enjoys camping trips and the person who loves yellow.
    for i in range(5):
        for j in range(5):
            if abs(i - j) == 2:  # One house between means |i-j| = 2
                s.add(Implies(vacation_vars[i] == Vacation.camping, color_vars[j] == Color.yellow))
                s.add(Implies(color_vars[j] == Color.yellow, vacation_vars[i] == Vacation.camping))
    
    # Check satisfiability
    if s.check() == sat:
        m = s.model()
        
        # Build result dictionary
        result = {"solution": {"header": ["House", "Name", "Vacation", "Education", "Color", "PhoneModel", "Food"], "rows": []}}
        
        # For each house, get the values
        for i in range(5):
            name_val = m.evaluate(name_vars[i])
            vacation_val = m.evaluate(vacation_vars[i])
            education_val = m.evaluate(education_vars[i])
            color_val = m.evaluate(color_vars[i])
            phone_val = m.evaluate(phone_vars[i])
            food_val = m.evaluate(food_vars[i])
            
            # Convert to string and remove namespace
            name_str = str(name_val).split('.')[1]
            vacation_str = str(vacation_val).split('.')[1]
            education_str = str(education_val).split('.')[1]
            color_str = str(color_val).split('.')[1]
            phone_str = str(phone_val).split('.')[1]
            food_str = str(food_val).split('.')[1]
            
            row = [str(i+1), name_str, vacation_str, education_str, color_str, phone_str, food_str]
            result["solution"]["rows"].append(row)
        
        # Output as JSON
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()