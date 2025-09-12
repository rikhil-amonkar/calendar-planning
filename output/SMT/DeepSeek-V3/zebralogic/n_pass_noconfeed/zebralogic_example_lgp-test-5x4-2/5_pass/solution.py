from z3 import *
import json

def main():
    # Create solver
    s = Solver()
    
    # Define the houses
    n = 5
    houses = [1, 2, 3, 4, 5]
    
    # Define attributes
    names = ['Bob', 'Eric', 'Arnold', 'Alice', 'Peter']
    colors = ['blue', 'green', 'white', 'yellow', 'red']
    phones = ['huawei p50', 'samsung galaxy s21', 'oneplus 9', 'iphone 13', 'google pixel 6']
    occupations = ['artist', 'teacher', 'doctor', 'engineer', 'lawyer']
    
    # Create variables for each attribute per house
    name_vars = [Int(f'name_{i}') for i in houses]
    color_vars = [Int(f'color_{i}') for i in houses]
    phone_vars = [Int(f'phone_{i}') for i in houses]
    occupation_vars = [Int(f'occupation_{i}') for i in houses]
    
    # Constrain all variables to be within their domain
    for i in houses:
        s.add(And(name_vars[i-1] >= 0, name_vars[i-1] < len(names)))
        s.add(And(color_vars[i-1] >= 0, color_vars[i-1] < len(colors)))
        s.add(And(phone_vars[i-1] >= 0, phone_vars[i-1] < len(phones)))
        s.add(And(occupation_vars[i-1] >= 0, occupation_vars[i-1] < len(occupations)))
    
    # All attributes must be unique per house
    s.add(Distinct(name_vars))
    s.add(Distinct(color_vars))
    s.add(Distinct(phone_vars))
    s.add(Distinct(occupation_vars))
    
    # Clue 1: The person who is an engineer is somewhere to the right of the person who is a lawyer.
    engineer_index = occupations.index('engineer')
    lawyer_index = occupations.index('lawyer')
    # Create a constraint that engineer is to the right of lawyer
    engineer_positions = [If(occupation_vars[i] == engineer_index, i+1, 0) for i in range(n)]
    lawyer_positions = [If(occupation_vars[i] == lawyer_index, i+1, 0) for i in range(n)]
    s.add(Sum(engineer_positions) > Sum(lawyer_positions))
    
    # Clue 2: Bob is in the second house.
    bob_index = names.index('Bob')
    s.add(name_vars[1] == bob_index)  # House 2 (index 1)
    
    # Clue 3: The person who uses a Samsung Galaxy S21 is the person who is a doctor.
    samsung_index = phones.index('samsung galaxy s21')
    doctor_index = occupations.index('doctor')
    for i in range(n):
        s.add(Implies(phone_vars[i] == samsung_index, occupation_vars[i] == doctor_index))
        s.add(Implies(occupation_vars[i] == doctor_index, phone_vars[i] == samsung_index))
    
    # Clue 4: The person who is a doctor is the person who loves blue.
    blue_index = colors.index('blue')
    for i in range(n):
        s.add(Implies(occupation_vars[i] == doctor_index, color_vars[i] == blue_index))
        s.add(Implies(color_vars[i] == blue_index, occupation_vars[i] == doctor_index))
    
    # Clue 5: The person whose favorite color is green is not in the fifth house.
    green_index = colors.index('green')
    s.add(color_vars[4] != green_index)
    
    # Clue 6: The person who is a lawyer is the person who uses a OnePlus 9.
    oneplus_index = phones.index('oneplus 9')
    for i in range(n):
        s.add(Implies(occupation_vars[i] == lawyer_index, phone_vars[i] == oneplus_index))
        s.add(Implies(phone_vars[i] == oneplus_index, occupation_vars[i] == lawyer_index))
    
    # Clue 7: The person who loves blue is directly left of the person whose favorite color is red.
    red_index = colors.index('red')
    blue_index = colors.index('blue')
    possibilities = []
    for i in range(n-1):
        possibilities.append(And(color_vars[i] == blue_index, color_vars[i+1] == red_index))
    s.add(Or(possibilities))
    
    # Clue 8: The person who is a lawyer is somewhere to the right of the person who uses a Samsung Galaxy S21.
    lawyer_pos = Int('lawyer_pos')
    samsung_pos = Int('samsung_pos')
    s.add(lawyer_pos == Sum([If(occupation_vars[i] == lawyer_index, i+1, 0) for i in range(n)]))
    s.add(samsung_pos == Sum([If(phone_vars[i] == samsung_index, i+1, 0) for i in range(n)]))
    s.add(lawyer_pos > samsung_pos)
    
    # Clue 9: There is one house between the person who uses a Google Pixel 6 and the person who uses a Huawei P50.
    google_index = phones.index('google pixel 6')
    huawei_index = phones.index('huawei p50')
    possibilities = []
    for i in range(n-2):
        # One house between means positions differ by 2
        possibilities.append(And(phone_vars[i] == google_index, phone_vars[i+2] == huawei_index))
        possibilities.append(And(phone_vars[i] == huawei_index, phone_vars[i+2] == google_index))
    s.add(Or(possibilities))
    
    # Clue 10: Arnold is the person who is an engineer.
    arnold_index = names.index('Arnold')
    for i in range(n):
        s.add(Implies(name_vars[i] == arnold_index, occupation_vars[i] == engineer_index))
        s.add(Implies(occupation_vars[i] == engineer_index, name_vars[i] == arnold_index))
    
    # Clue 11: Alice is the person who loves yellow.
    alice_index = names.index('Alice')
    yellow_index = colors.index('yellow')
    for i in range(n):
        s.add(Implies(name_vars[i] == alice_index, color_vars[i] == yellow_index))
        s.add(Implies(color_vars[i] == yellow_index, name_vars[i] == alice_index))
    
    # Clue 12: The person who uses a Google Pixel 6 is Eric.
    eric_index = names.index('Eric')
    google_index = phones.index('google pixel 6')
    for i in range(n):
        s.add(Implies(phone_vars[i] == google_index, name_vars[i] == eric_index))
        s.add(Implies(name_vars[i] == eric_index, phone_vars[i] == google_index))
    
    # Clue 13: The person who uses a Google Pixel 6 is the person who is a teacher.
    teacher_index = occupations.index('teacher')
    for i in range(n):
        s.add(Implies(phone_vars[i] == google_index, occupation_vars[i] == teacher_index))
        s.add(Implies(occupation_vars[i] == teacher_index, phone_vars[i] == google_index))
    
    # Clue 14: The person whose favorite color is red is somewhere to the right of the person who is a teacher.
    red_pos = Int('red_pos')
    teacher_pos = Int('teacher_pos')
    s.add(red_pos == Sum([If(color_vars[i] == red_index, i+1, 0) for i in range(n)]))
    s.add(teacher_pos == Sum([If(occupation_vars[i] == teacher_index, i+1, 0) for i in range(n)]))
    s.add(red_pos > teacher_pos)
    
    # Check for solution
    if s.check() == sat:
        model = s.model()
        
        # Prepare result data
        result = {
            "solution": {
                "header": ["House", "Name", "Color", "PhoneModel", "Occupation"],
                "rows": []
            }
        }
        
        # Extract values for each house
        for i in range(n):
            house_num = str(i + 1)
            name_val = names[model.evaluate(name_vars[i]).as_long()]
            color_val = colors[model.evaluate(color_vars[i]).as_long()]
            phone_val = phones[model.evaluate(phone_vars[i]).as_long()]
            occupation_val = occupations[model.evaluate(occupation_vars[i]).as_long()]
            
            result["solution"]["rows"].append([house_num, name_val, color_val, phone_val, occupation_val])
        
        # Output as JSON
        print(json.dumps(result, indent=2))
    else:
        print('No solution found')

if __name__ == "__main__":
    main()