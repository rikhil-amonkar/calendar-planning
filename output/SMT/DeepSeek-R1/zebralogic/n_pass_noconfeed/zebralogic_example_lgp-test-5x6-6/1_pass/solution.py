import json
from z3 import *

def main():
    # Define the categories and their values
    names = ['Arnold', 'Eric', 'Alice', 'Bob', 'Peter']
    vacations = ['mountain', 'city', 'cruise', 'beach', 'camping']
    educations = ['doctorate', 'high school', 'bachelor', 'associate', 'master']
    colors = ['blue', 'red', 'white', 'yellow', 'green']
    phones = ['google pixel 6', 'iphone 13', 'oneplus 9', 'huawei p50', 'samsung galaxy s21']
    foods = ['grilled cheese', 'stir fry', 'pizza', 'spaghetti', 'stew']
    
    # Create solver
    s = Solver()
    
    # Create integer variables for each attribute in each house
    name_vars = [Int(f"name_{i}") for i in range(5)]
    vacation_vars = [Int(f"vacation_{i}") for i in range(5)]
    education_vars = [Int(f"education_{i}") for i in range(5)]
    color_vars = [Int(f"color_{i}") for i in range(5)]
    phone_vars = [Int(f"phone_{i}") for i in range(5)]
    food_vars = [Int(f"food_{i}") for i in range(5)]
    
    # Constrain each attribute to have distinct values
    s.add(Distinct(name_vars))
    s.add(Distinct(vacation_vars))
    s.add(Distinct(education_vars))
    s.add(Distinct(color_vars))
    s.add(Distinct(phone_vars))
    s.add(Distinct(food_vars))
    
    # Each variable should be within 0-4 (index of possible values)
    for i in range(5):
        s.add(name_vars[i] >= 0, name_vars[i] < 5)
        s.add(vacation_vars[i] >= 0, vacation_vars[i] < 5)
        s.add(education_vars[i] >= 0, education_vars[i] < 5)
        s.add(color_vars[i] >= 0, color_vars[i] < 5)
        s.add(phone_vars[i] >= 0, phone_vars[i] < 5)
        s.add(food_vars[i] >= 0, food_vars[i] < 5)
    
    # Clue 1: The person who loves the stew is not in the first house.
    s.add(food_vars[0] != foods.index('stew'))
    
    # Clue 2: There are two houses between the person who loves stir fry and the person with an associate's degree.
    for i in range(5):
        for j in range(5):
            if abs(i - j) == 3:
                s.add(Implies(food_vars[i] == foods.index('stir fry'), education_vars[j] == educations.index('associate')))
                s.add(Implies(education_vars[i] == educations.index('associate'), food_vars[j] == foods.index('stir fry')))
    
    # Clue 3: The person who enjoys mountain retreats is the person with a bachelor's degree.
    for i in range(5):
        s.add(Implies(vacation_vars[i] == vacations.index('mountain'), education_vars[i] == educations.index('bachelor')))
    
    # Clue 4: The person with a doctorate is somewhere to the right of Bob.
    bob_index = Int('bob_index')
    s.add(bob_index >= 0, bob_index < 5)
    for i in range(5):
        s.add(Implies(name_vars[i] == names.index('Bob'), bob_index == i))
    doctorate_index = Int('doctorate_index')
    s.add(doctorate_index >= 0, doctorate_index < 5)
    for i in range(5):
        s.add(Implies(education_vars[i] == educations.index('doctorate'), doctorate_index == i))
    s.add(doctorate_index > bob_index)
    
    # Clue 5: The person who uses a Samsung Galaxy S21 is in the third house.
    s.add(phone_vars[2] == phones.index('samsung galaxy s21'))
    
    # Clue 6: Eric is the person with a doctorate.
    for i in range(5):
        s.add(Implies(name_vars[i] == names.index('Eric'), education_vars[i] == educations.index('doctorate')))
    
    # Clue 7: The person with a doctorate is in the third house.
    s.add(education_vars[2] == educations.index('doctorate'))
    
    # Clue 8: The person who loves stir fry is the person with a bachelor's degree.
    for i in range(5):
        s.add(Implies(food_vars[i] == foods.index('stir fry'), education_vars[i] == educations.index('bachelor')))
    
    # Clue 9: The person with a doctorate is the person who is a pizza lover.
    for i in range(5):
        s.add(Implies(education_vars[i] == educations.index('doctorate'), food_vars[i] == foods.index('pizza')))
    
    # Clue 10: The person whose favorite color is green is somewhere to the right of Peter.
    peter_index = Int('peter_index')
    s.add(peter_index >= 0, peter_index < 5)
    for i in range(5):
        s.add(Implies(name_vars[i] == names.index('Peter'), peter_index == i))
    green_index = Int('green_index')
    s.add(green_index >= 0, green_index < 5)
    for i in range(5):
        s.add(Implies(color_vars[i] == colors.index('green'), green_index == i))
    s.add(green_index > peter_index)
    
    # Clue 11: The person who enjoys camping trips is the person who uses an iPhone 13.
    for i in range(5):
        s.add(Implies(vacation_vars[i] == vacations.index('camping'), phone_vars[i] == phones.index('iphone 13')))
    
    # Clue 12: The person who likes going on cruises is Alice.
    for i in range(5):
        s.add(Implies(vacation_vars[i] == vacations.index('cruise'), name_vars[i] == names.index('Alice')))
    
    # Clue 13: There is one house between the person with a high school diploma and the person who uses a Samsung Galaxy S21.
    for i in range(5):
        if abs(i - 2) == 2:
            s.add(education_vars[i] == educations.index('high school'))
        else:
            s.add(education_vars[i] != educations.index('high school'))
    
    # Clue 14: The person who uses a Google Pixel 6 is Arnold.
    for i in range(5):
        s.add(Implies(phone_vars[i] == phones.index('google pixel 6'), name_vars[i] == names.index('Arnold')))
    
    # Clue 15: The person who uses a OnePlus 9 is somewhere to the right of the person who uses a Huawei P50.
    huawei_index = Int('huawei_index')
    s.add(huawei_index >= 0, huawei_index < 5)
    for i in range(5):
        s.add(Implies(phone_vars[i] == phones.index('huawei p50'), huawei_index == i))
    oneplus_index = Int('oneplus_index')
    s.add(oneplus_index >= 0, oneplus_index < 5)
    for i in range(5):
        s.add(Implies(phone_vars[i] == phones.index('oneplus 9'), oneplus_index == i))
    s.add(oneplus_index > huawei_index)
    
    # Clue 16: Arnold is the person who loves eating grilled cheese.
    for i in range(5):
        s.add(Implies(name_vars[i] == names.index('Arnold'), food_vars[i] == foods.index('grilled cheese')))
    
    # Clue 17: The person who loves eating grilled cheese is not in the fourth house.
    s.add(food_vars[3] != foods.index('grilled cheese'))
    
    # Clue 18: There are two houses between the person with a bachelor's degree and the person whose favorite color is red.
    bachelor_index = Int('bachelor_index')
    s.add(bachelor_index >= 0, bachelor_index < 5)
    for i in range(5):
        s.add(Implies(education_vars[i] == educations.index('bachelor'), bachelor_index == i))
    red_index = Int('red_index')
    s.add(red_index >= 0, red_index < 5)
    for i in range(5):
        s.add(Implies(color_vars[i] == colors.index('red'), red_index == i))
    s.add(Or(bachelor_index - red_index == 3, red_index - bachelor_index == 3))
    
    # Clue 19: The person who loves beach vacations is somewhere to the right of the person who prefers city breaks.
    city_index = Int('city_index')
    s.add(city_index >= 0, city_index < 5)
    for i in range(5):
        s.add(Implies(vacation_vars[i] == vacations.index('city'), city_index == i))
    beach_index = Int('beach_index')
    s.add(beach_index >= 0, beach_index < 5)
    for i in range(5):
        s.add(Implies(vacation_vars[i] == vacations.index('beach'), beach_index == i))
    s.add(beach_index > city_index)
    
    # Clue 20: The person whose favorite color is green is not in the second house.
    s.add(color_vars[1] != colors.index('green'))
    
    # Clue 21: The person who loves blue is somewhere to the right of Peter.
    blue_index = Int('blue_index')
    s.add(blue_index >= 0, blue_index < 5)
    for i in range(5):
        s.add(Implies(color_vars[i] == colors.index('blue'), blue_index == i))
    s.add(blue_index > peter_index)
    
    # Clue 22: There is one house between the person who enjoys camping trips and the person who loves yellow.
    camping_index = Int('camping_index')
    s.add(camping_index >= 0, camping_index < 5)
    for i in range(5):
        s.add(Implies(vacation_vars[i] == vacations.index('camping'), camping_index == i))
    yellow_index = Int('yellow_index')
    s.add(yellow_index >= 0, yellow_index < 5)
    for i in range(5):
        s.add(Implies(color_vars[i] == colors.index('yellow'), yellow_index == i))
    s.add(Or(camping_index - yellow_index == 2, yellow_index - camping_index == 2))
    
    # Check for solution
    if s.check() == sat:
        m = s.model()
        result = []
        for i in range(5):
            house_num = str(i+1)
            name_val = names[m.evaluate(name_vars[i]).as_long()]
            vacation_val = vacations[m.evaluate(vacation_vars[i]).as_long()]
            education_val = educations[m.evaluate(education_vars[i]).as_long()]
            color_val = colors[m.evaluate(color_vars[i]).as_long()]
            phone_val = phones[m.evaluate(phone_vars[i]).as_long()]
            food_val = foods[m.evaluate(food_vars[i]).as_long()]
            result.append([house_num, name_val, vacation_val, education_val, color_val, phone_val, food_val])
        
        output = {
            "solution": {
                "header": ["House", "Name", "Vacation", "Education", "Color", "PhoneModel", "Food"],
                "rows": result
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()