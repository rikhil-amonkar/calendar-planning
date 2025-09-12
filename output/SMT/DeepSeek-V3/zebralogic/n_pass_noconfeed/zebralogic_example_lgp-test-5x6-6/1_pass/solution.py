from z3 import *
import json

def main():
    solver = Solver()
    
    n = 5
    houses = [1, 2, 3, 4, 5]
    
    # Define attributes
    names = ['Arnold', 'Eric', 'Alice', 'Bob', 'Peter']
    vacations = ['mountain', 'city', 'cruise', 'beach', 'camping']
    educations = ['doctorate', 'high school', 'bachelor', 'associate', 'master']
    colors = ['blue', 'red', 'white', 'yellow', 'green']
    phones = ['google pixel 6', 'iphone 13', 'oneplus 9', 'huawei p50', 'samsung galaxy s21']
    foods = ['grilled cheese', 'stir fry', 'pizza', 'spaghetti', 'stew']
    
    # Create variables for each attribute per house
    name_vars = [Int(f'name_{i}') for i in houses]
    vacation_vars = [Int(f'vacation_{i}') for i in houses]
    education_vars = [Int(f'education_{i}') for i in houses]
    color_vars = [Int(f'color_{i}') for i in houses]
    phone_vars = [Int(f'phone_{i}') for i in houses]
    food_vars = [Int(f'food_{i}') for i in houses]
    
    # Domain constraints for each attribute
    for i in houses:
        solver.add(And(name_vars[i-1] >= 0, name_vars[i-1] < len(names)))
        solver.add(And(vacation_vars[i-1] >= 0, vacation_vars[i-1] < len(vacations)))
        solver.add(And(education_vars[i-1] >= 0, education_vars[i-1] < len(educations)))
        solver.add(And(color_vars[i-1] >= 0, color_vars[i-1] < len(colors)))
        solver.add(And(phone_vars[i-1] >= 0, phone_vars[i-1] < len(phones)))
        solver.add(And(food_vars[i-1] >= 0, food_vars[i-1] < len(foods)))
    
    # All attributes are distinct per house
    solver.add(Distinct(name_vars))
    solver.add(Distinct(vacation_vars))
    solver.add(Distinct(education_vars))
    solver.add(Distinct(color_vars))
    solver.add(Distinct(phone_vars))
    solver.add(Distinct(food_vars))
    
    # Clue 1: The person who loves the stew is not in the first house.
    stew_index = foods.index('stew')
    solver.add(food_vars[0] != stew_index)
    
    # Clue 2: There are two houses between the person who loves stir fry and the person with an associate's degree.
    stir_fry_index = foods.index('stir fry')
    associate_index = educations.index('associate')
    for i in houses:
        for j in houses:
            if abs(i - j) == 3:  # Two houses between means difference of 3
                solver.add(Implies(food_vars[i-1] == stir_fry_index, education_vars[j-1] == associate_index))
                solver.add(Implies(education_vars[j-1] == associate_index, food_vars[i-1] == stir_fry_index))
    
    # Clue 3: The person who enjoys mountain retreats is the person with a bachelor's degree.
    mountain_index = vacations.index('mountain')
    bachelor_index = educations.index('bachelor')
    for i in houses:
        solver.add(Implies(vacation_vars[i-1] == mountain_index, education_vars[i-1] == bachelor_index))
        solver.add(Implies(education_vars[i-1] == bachelor_index, vacation_vars[i-1] == mountain_index))
    
    # Clue 4: The person with a doctorate is somewhere to the right of Bob.
    doctorate_index = educations.index('doctorate')
    bob_index = names.index('Bob')
    for i in houses:
        for j in houses:
            if j > i:  # j is right of i
                solver.add(Implies(name_vars[i-1] == bob_index, education_vars[j-1] == doctorate_index))
    
    # Clue 5: The person who uses a Samsung Galaxy S21 is in the third house.
    samsung_index = phones.index('samsung galaxy s21')
    solver.add(phone_vars[2] == samsung_index)
    
    # Clue 6: Eric is the person with a doctorate.
    eric_index = names.index('Eric')
    for i in houses:
        solver.add(Implies(name_vars[i-1] == eric_index, education_vars[i-1] == doctorate_index))
        solver.add(Implies(education_vars[i-1] == doctorate_index, name_vars[i-1] == eric_index))
    
    # Clue 7: The person with a doctorate is in the third house.
    solver.add(education_vars[2] == doctorate_index)
    
    # Clue 8: The person who loves stir fry is the person with a bachelor's degree.
    for i in houses:
        solver.add(Implies(food_vars[i-1] == stir_fry_index, education_vars[i-1] == bachelor_index))
        solver.add(Implies(education_vars[i-1] == bachelor_index, food_vars[i-1] == stir_fry_index))
    
    # Clue 9: The person with a doctorate is the person who is a pizza lover.
    pizza_index = foods.index('pizza')
    for i in houses:
        solver.add(Implies(education_vars[i-1] == doctorate_index, food_vars[i-1] == pizza_index))
        solver.add(Implies(food_vars[i-1] == pizza_index, education_vars[i-1] == doctorate_index))
    
    # Clue 10: The person whose favorite color is green is somewhere to the right of Peter.
    green_index = colors.index('green')
    peter_index = names.index('Peter')
    for i in houses:
        for j in houses:
            if j > i:  # j is right of i
                solver.add(Implies(name_vars[i-1] == peter_index, color_vars[j-1] == green_index))
    
    # Clue 11: The person who enjoys camping trips is the person who uses an iPhone 13.
    camping_index = vacations.index('camping')
    iphone_index = phones.index('iphone 13')
    for i in houses:
        solver.add(Implies(vacation_vars[i-1] == camping_index, phone_vars[i-1] == iphone_index))
        solver.add(Implies(phone_vars[i-1] == iphone_index, vacation_vars[i-1] == camping_index))
    
    # Clue 12: The person who likes going on cruises is Alice.
    cruise_index = vacations.index('cruise')
    alice_index = names.index('Alice')
    for i in houses:
        solver.add(Implies(vacation_vars[i-1] == cruise_index, name_vars[i-1] == alice_index))
        solver.add(Implies(name_vars[i-1] == alice_index, vacation_vars[i-1] == cruise_index))
    
    # Clue 13: There is one house between the person with a high school diploma and the person who uses a Samsung Galaxy S21.
    high_school_index = educations.index('high school')
    for i in houses:
        for j in houses:
            if abs(i - j) == 2:  # One house between means difference of 2
                solver.add(Implies(education_vars[i-1] == high_school_index, phone_vars[j-1] == samsung_index))
                solver.add(Implies(phone_vars[j-1] == samsung_index, education_vars[i-1] == high_school_index))
    
    # Clue 14: The person who uses a Google Pixel 6 is Arnold.
    google_index = phones.index('google pixel 6')
    arnold_index = names.index('Arnold')
    for i in houses:
        solver.add(Implies(phone_vars[i-1] == google_index, name_vars[i-1] == arnold_index))
        solver.add(Implies(name_vars[i-1] == arnold_index, phone_vars[i-1] == google_index))
    
    # Clue 15: The person who uses a OnePlus 9 is somewhere to the right of the person who uses a Huawei P50.
    oneplus_index = phones.index('oneplus 9')
    huawei_index = phones.index('huawei p50')
    for i in houses:
        for j in houses:
            if j > i:  # j is right of i
                solver.add(Implies(phone_vars[i-1] == huawei_index, phone_vars[j-1] == oneplus_index))
    
    # Clue 16: Arnold is the person who loves eating grilled cheese.
    grilled_cheese_index = foods.index('grilled cheese')
    for i in houses:
        solver.add(Implies(name_vars[i-1] == arnold_index, food_vars[i-1] == grilled_cheese_index))
        solver.add(Implies(food_vars[i-1] == grilled_cheese_index, name_vars[i-1] == arnold_index))
    
    # Clue 17: The person who loves eating grilled cheese is not in the fourth house.
    solver.add(food_vars[3] != grilled_cheese_index)
    
    # Clue 18: There are two houses between the person with a bachelor's degree and the person whose favorite color is red.
    red_index = colors.index('red')
    for i in houses:
        for j in houses:
            if abs(i - j) == 3:  # Two houses between means difference of 3
                solver.add(Implies(education_vars[i-1] == bachelor_index, color_vars[j-1] == red_index))
                solver.add(Implies(color_vars[j-1] == red_index, education_vars[i-1] == bachelor_index))
    
    # Clue 19: The person who loves beach vacations is somewhere to the right of the person who prefers city breaks.
    beach_index = vacations.index('beach')
    city_index = vacations.index('city')
    for i in houses:
        for j in houses:
            if j > i:  # j is right of i
                solver.add(Implies(vacation_vars[i-1] == city_index, vacation_vars[j-1] == beach_index))
    
    # Clue 20: The person whose favorite color is green is not in the second house.
    solver.add(color_vars[1] != green_index)
    
    # Clue 21: The person who loves blue is somewhere to the right of Peter.
    blue_index = colors.index('blue')
    for i in houses:
        for j in houses:
            if j > i:  # j is right of i
                solver.add(Implies(name_vars[i-1] == peter_index, color_vars[j-1] == blue_index))
    
    # Clue 22: There is one house between the person who enjoys camping trips and the person who loves yellow.
    yellow_index = colors.index('yellow')
    for i in houses:
        for j in houses:
            if abs(i - j) == 2:  # One house between means difference of 2
                solver.add(Implies(vacation_vars[i-1] == camping_index, color_vars[j-1] == yellow_index))
                solver.add(Implies(color_vars[j-1] == yellow_index, vacation_vars[i-1] == camping_index))
    
    # Solve the constraints
    if solver.check() == sat:
        model = solver.model()
        
        # Create result dictionary
        result = {
            "solution": {
                "header": ["House", "Name", "Vacation", "Education", "Color", "PhoneModel", "Food"],
                "rows": []
            }
        }
        
        # Extract values for each house
        for i in range(1, n+1):
            name_val = model.evaluate(name_vars[i-1])
            vacation_val = model.evaluate(vacation_vars[i-1])
            education_val = model.evaluate(education_vars[i-1])
            color_val = model.evaluate(color_vars[i-1])
            phone_val = model.evaluate(phone_vars[i-1])
            food_val = model.evaluate(food_vars[i-1])
            
            # Convert to actual values
            name = names[name_val.as_long()]
            vacation = vacations[vacation_val.as_long()]
            education = educations[education_val.as_long()]
            color = colors[color_val.as_long()]
            phone = phones[phone_val.as_long()]
            food = foods[food_val.as_long()]
            
            result["solution"]["rows"].append([str(i), name, vacation, education, color, phone, food])
        
        print(json.dumps(result, indent=2))
    else:
        print('No solution found')

if __name__ == "__main__":
    main()