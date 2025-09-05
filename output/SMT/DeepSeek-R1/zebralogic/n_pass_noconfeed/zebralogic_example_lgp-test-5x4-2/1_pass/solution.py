import z3
import json

def main():
    # Define the sorts for each attribute
    Name = z3.EnumSort('Name', ['Bob', 'Eric', 'Arnold', 'Alice', 'Peter'])
    Color = z3.EnumSort('Color', ['blue', 'green', 'white', 'yellow', 'red'])
    PhoneModel = z3.EnumSort('PhoneModel', ['huawei p50', 'samsung galaxy s21', 'oneplus 9', 'iphone 13', 'google pixel 6'])
    Occupation = z3.EnumSort('Occupation', ['artist', 'teacher', 'doctor', 'engineer', 'lawyer'])
    
    # Extract the constants for each attribute value
    Bob, Eric, Arnold, Alice, Peter = Name
    blue, green, white, yellow, red = Color
    huawei_p50, samsung_galaxy_s21, oneplus_9, iphone_13, google_pixel_6 = PhoneModel
    artist, teacher, doctor, engineer, lawyer = Occupation

    # Create arrays for each attribute for the 5 houses (indexed 0-4)
    names = [z3.Const(f'name_{i}', Name) for i in range(5)]
    colors = [z3.Const(f'color_{i}', Color) for i in range(5)]
    phones = [z3.Const(f'phone_{i}', PhoneModel) for i in range(5)]
    occupations = [z3.Const(f'occupation_{i}', Occupation) for i in range(5)]

    solver = z3.Solver()

    # All attributes must have distinct values
    solver.add(z3.Distinct(names))
    solver.add(z3.Distinct(colors))
    solver.add(z3.Distinct(phones))
    solver.add(z3.Distinct(occupations))

    # Clue 2: Bob is in the second house (index 1)
    solver.add(names[1] == Bob)

    # Clue 3: Samsung Galaxy S21 user is doctor
    for i in range(5):
        solver.add(z3.Implies(phones[i] == samsung_galaxy_s21, occupations[i] == doctor))

    # Clue 4: Doctor loves blue
    for i in range(5):
        solver.add(z3.Implies(occupations[i] == doctor, colors[i] == blue))

    # Clue 5: Green color not in fifth house (index 4)
    solver.add(colors[4] != green)

    # Clue 6: Lawyer uses OnePlus 9
    for i in range(5):
        solver.add(z3.Implies(occupations[i] == lawyer, phones[i] == oneplus_9))

    # Clue 7: Blue directly left of Red
    for i in range(4):
        solver.add(z3.Implies(colors[i] == blue, colors[i+1] == red))
    solver.add(z3.Or([colors[i] == blue for i in range(4)]))  # Ensure blue exists and isn't in last house

    # Clue 8: Lawyer is right of Samsung Galaxy S21 user
    # First, find indices for lawyer and samsung
    lawyer_index = z3.Int('lawyer_index')
    samsung_index = z3.Int('samsung_index')
    solver.add(lawyer_index >= 0, lawyer_index < 5)
    solver.add(samsung_index >= 0, samsung_index < 5)
    for i in range(5):
        solver.add(z3.Implies(occupations[i] == lawyer, lawyer_index == i))
        solver.add(z3.Implies(phones[i] == samsung_galaxy_s21, samsung_index == i))
    solver.add(lawyer_index > samsung_index)

    # Clue 9: One house between Google Pixel 6 and Huawei P50
    pixel_index = z3.Int('pixel_index')
    huawei_index = z3.Int('huawei_index')
    solver.add(pixel_index >= 0, pixel_index < 5)
    solver.add(huawei_index >= 0, huawei_index < 5)
    for i in range(5):
        solver.add(z3.Implies(phones[i] == google_pixel_6, pixel_index == i))
        solver.add(z3.Implies(phones[i] == huawei_p50, huawei_index == i))
    solver.add(z3.Or(pixel_index == huawei_index + 2, pixel_index == huawei_index - 2))

    # Clue 10: Arnold is engineer
    for i in range(5):
        solver.add(z3.Implies(names[i] == Arnold, occupations[i] == engineer))

    # Clue 11: Alice loves yellow
    for i in range(5):
        solver.add(z3.Implies(names[i] == Alice, colors[i] == yellow))

    # Clue 12: Google Pixel 6 user is Eric
    for i in range(5):
        solver.add(z3.Implies(phones[i] == google_pixel_6, names[i] == Eric))

    # Clue 13: Google Pixel 6 user is teacher
    for i in range(5):
        solver.add(z3.Implies(phones[i] == google_pixel_6, occupations[i] == teacher))

    # Clue 14: Red color is right of teacher
    teacher_index = z3.Int('teacher_index')
    red_index = z3.Int('red_index')
    solver.add(teacher_index >= 0, teacher_index < 5)
    solver.add(red_index >= 0, red_index < 5)
    for i in range(5):
        solver.add(z3.Implies(occupations[i] == teacher, teacher_index == i))
        solver.add(z3.Implies(colors[i] == red, red_index == i))
    solver.add(red_index > teacher_index)

    # Clue 1: Engineer is right of lawyer
    engineer_index = z3.Int('engineer_index')
    solver.add(engineer_index >= 0, engineer_index < 5)
    for i in range(5):
        solver.add(z3.Implies(occupations[i] == engineer, engineer_index == i))
    solver.add(engineer_index > lawyer_index)

    # Check and get the model
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Prepare the result table
        header = ["House", "Name", "Color", "PhoneModel", "Occupation"]
        rows = []
        
        # Map house indices to attribute values
        for i in range(5):
            house_num = str(i+1)
            name_val = str(model.evaluate(names[i]))
            color_val = str(model.evaluate(colors[i]))
            phone_val = str(model.evaluate(phones[i]))
            occupation_val = str(model.evaluate(occupations[i]))
            rows.append([house_num, name_val, color_val, phone_val, occupation_val])
        
        # Create the solution dictionary
        solution_dict = {
            "solution": {
                "header": header,
                "rows": rows
            }
        }
        
        # Output as JSON
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()