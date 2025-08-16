from z3 import Datatype, Solver, Consts, Distinct, Or, And, Not, Implies, If
import json

def main():
    # Define data types for attributes
    Name = Datatype('Name')
    Name.declare('Bob')
    Name.declare('Eric')
    Name.declare('Arnold')
    Name.declare('Alice')
    Name.declare('Peter')
    Name = Name.create()
    
    Color = Datatype('Color')
    Color.declare('blue')
    Color.declare('green')
    Color.declare('white')
    Color.declare('yellow')
    Color.declare('red')
    Color = Color.create()
    
    PhoneModel = Datatype('PhoneModel')
    PhoneModel.declare('huawei_p50')
    PhoneModel.declare('samsung_galaxy_s21')
    PhoneModel.declare('oneplus_9')
    PhoneModel.declare('iphone_13')
    PhoneModel.declare('google_pixel_6')
    PhoneModel = PhoneModel.create()
    
    Occupation = Datatype('Occupation')
    Occupation.declare('artist')
    Occupation.declare('teacher')
    Occupation.declare('doctor')
    Occupation.declare('engineer')
    Occupation.declare('lawyer')
    Occupation = Occupation.create()
    
    # Create lists for attributes of each house
    names = Consts('n1 n2 n3 n4 n5', Name)
    colors = Consts('c1 c2 c3 c4 c5', Color)
    phones = Consts('p1 p2 p3 p4 p5', PhoneModel)
    occupations = Consts('o1 o2 o3 o4 o5', Occupation)
    
    s = Solver()
    
    # Each attribute must be unique
    s.add(Distinct(names))
    s.add(Distinct(colors))
    s.add(Distinct(phones))
    s.add(Distinct(occupations))
    
    # Clue 2: Bob is in the second house.
    s.add(names[1] == Name.Bob)
    
    # Clue 3: The person who uses a Samsung Galaxy S21 is the person who is a doctor.
    for i in range(5):
        s.add((phones[i] == PhoneModel.samsung_galaxy_s21) == (occupations[i] == Occupation.doctor))
    
    # Clue 4: The person who is a doctor is the person who loves blue.
    for i in range(5):
        s.add((occupations[i] == Occupation.doctor) == (colors[i] == Color.blue))
    
    # Clue 5: The person whose favorite color is green is not in the fifth house.
    s.add(colors[4] != Color.green)
    
    # Clue 6: The person who is a lawyer is the person who uses a OnePlus 9.
    for i in range(5):
        s.add((occupations[i] == Occupation.lawyer) == (phones[i] == PhoneModel.oneplus_9))
    
    # Clue 7: The person who loves blue is directly left of the person whose favorite color is red.
    blue_left_red = Or(
        And(colors[0] == Color.blue, colors[1] == Color.red),
        And(colors[1] == Color.blue, colors[2] == Color.red),
        And(colors[2] == Color.blue, colors[3] == Color.red),
        And(colors[3] == Color.blue, colors[4] == Color.red)
    )
    s.add(blue_left_red)
    
    # Clue 8: The person who is a lawyer is somewhere to the right of the person who uses a Samsung Galaxy S21.
    lawyer_right_samsung = Or(
        And(phones[0] == PhoneModel.samsung_galaxy_s21, occupations[1] == Occupation.lawyer, 0<1),
        And(phones[0] == PhoneModel.samsung_galaxy_s21, occupations[2] == Occupation.lawyer, 0<2),
        And(phones[0] == PhoneModel.samsung_galaxy_s21, occupations[3] == Occupation.lawyer, 0<3),
        And(phones[0] == PhoneModel.samsung_galaxy_s21, occupations[4] == Occupation.lawyer, 0<4),
        And(phones[1] == PhoneModel.samsung_galaxy_s21, occupations[2] == Occupation.lawyer, 1<2),
        And(phones[1] == PhoneModel.samsung_galaxy_s21, occupations[3] == Occupation.lawyer, 1<3),
        And(phones[1] == PhoneModel.samsung_galaxy_s21, occupations[4] == Occupation.lawyer, 1<4),
        And(phones[2] == PhoneModel.samsung_galaxy_s21, occupations[3] == Occupation.lawyer, 2<3),
        And(phones[2] == PhoneModel.samsung_galaxy_s21, occupations[4] == Occupation.lawyer, 2<4),
        And(phones[3] == PhoneModel.samsung_galaxy_s21, occupations[4] == Occupation.lawyer, 3<4)
    )
    s.add(lawyer_right_samsung)
    
    # Clue 9: There is one house between the person who uses a Google Pixel 6 and the person who uses a Huawei P50.
    phone_gap = Or(
        And(phones[0] == PhoneModel.google_pixel_6, phones[2] == PhoneModel.huawei_p50),
        And(phones[1] == PhoneModel.google_pixel_6, phones[3] == PhoneModel.huawei_p50),
        And(phones[2] == PhoneModel.google_pixel_6, phones[4] == PhoneModel.huawei_p50),
        And(phones[0] == PhoneModel.huawei_p50, phones[2] == PhoneModel.google_pixel_6),
        And(phones[1] == PhoneModel.huawei_p50, phones[3] == PhoneModel.google_pixel_6),
        And(phones[2] == PhoneModel.huawei_p50, phones[4] == PhoneModel.google_pixel_6)
    )
    s.add(phone_gap)
    
    # Clue 10: Arnold is the person who is an engineer.
    for i in range(5):
        s.add((names[i] == Name.Arnold) == (occupations[i] == Occupation.engineer))
    
    # Clue 11: Alice is the person who loves yellow.
    for i in range(5):
        s.add((names[i] == Name.Alice) == (colors[i] == Color.yellow))
    
    # Clue 12: The person who uses a Google Pixel 6 is Eric.
    for i in range(5):
        s.add((phones[i] == PhoneModel.google_pixel_6) == (names[i] == Name.Eric))
    
    # Clue 13: The person who uses a Google Pixel 6 is the person who is a teacher.
    for i in range(5):
        s.add((phones[i] == PhoneModel.google_pixel_6) == (occupations[i] == Occupation.teacher))
    
    # Clue 14: The person whose favorite color is red is somewhere to the right of the person who is a teacher.
    red_right_teacher = Or(
        And(occupations[0] == Occupation.teacher, colors[1] == Color.red, 0<1),
        And(occupations[0] == Occupation.teacher, colors[2] == Color.red, 0<2),
        And(occupations[0] == Occupation.teacher, colors[3] == Color.red, 0<3),
        And(occupations[0] == Occupation.teacher, colors[4] == Color.red, 0<4),
        And(occupations[1] == Occupation.teacher, colors[2] == Color.red, 1<2),
        And(occupations[1] == Occupation.teacher, colors[3] == Color.red, 1<3),
        And(occupations[1] == Occupation.teacher, colors[4] == Color.red, 1<4),
        And(occupations[2] == Occupation.teacher, colors[3] == Color.red, 2<3),
        And(occupations[2] == Occupation.teacher, colors[4] == Color.red, 2<4),
        And(occupations[3] == Occupation.teacher, colors[4] == Color.red, 3<4)
    )
    s.add(red_right_teacher)
    
    # Clue 1: The person who is an engineer is somewhere to the right of the person who is a lawyer.
    engineer_right_lawyer = Or(
        And(occupations[0] == Occupation.lawyer, occupations[1] == Occupation.engineer, 0<1),
        And(occupations[0] == Occupation.lawyer, occupations[2] == Occupation.engineer, 0<2),
        And(occupations[0] == Occupation.lawyer, occupations[3] == Occupation.engineer, 0<3),
        And(occupations[0] == Occupation.lawyer, occupations[4] == Occupation.engineer, 0<4),
        And(occupations[1] == Occupation.lawyer, occupations[2] == Occupation.engineer, 1<2),
        And(occupations[1] == Occupation.lawyer, occupations[3] == Occupation.engineer, 1<3),
        And(occupations[1] == Occupation.lawyer, occupations[4] == Occupation.engineer, 1<4),
        And(occupations[2] == Occupation.lawyer, occupations[3] == Occupation.engineer, 2<3),
        And(occupations[2] == Occupation.lawyer, occupations[4] == Occupation.engineer, 2<4),
        And(occupations[3] == Occupation.lawyer, occupations[4] == Occupation.engineer, 3<4)
    )
    s.add(engineer_right_lawyer)
    
    # Check for solution
    if s.check() == sat:
        m = s.model()
        
        # Mapping Z3 constants to string representations
        def name_str(x):
            if x == Name.Bob: return "Bob"
            elif x == Name.Eric: return "Eric"
            elif x == Name.Arnold: return "Arnold"
            elif x == Name.Alice: return "Alice"
            elif x == Name.Peter: return "Peter"
        
        def color_str(x):
            if x == Color.blue: return "blue"
            elif x == Color.green: return "green"
            elif x == Color.white: return "white"
            elif x == Color.yellow: return "yellow"
            elif x == Color.red: return "red"
        
        def phone_str(x):
            if x == PhoneModel.huawei_p50: return "huawei p50"
            elif x == PhoneModel.samsung_galaxy_s21: return "samsung galaxy s21"
            elif x == PhoneModel.oneplus_9: return "oneplus 9"
            elif x == PhoneModel.iphone_13: return "iphone 13"
            elif x == PhoneModel.google_pixel_6: return "google pixel 6"
        
        def occupation_str(x):
            if x == Occupation.artist: return "artist"
            elif x == Occupation.teacher: return "teacher"
            elif x == Occupation.doctor: return "doctor"
            elif x == Occupation.engineer: return "engineer"
            elif x == Occupation.lawyer: return "lawyer"
        
        # Build the rows for the solution
        rows = []
        for i in range(5):
            house = str(i+1)
            n = name_str(m[names[i]].as_long())
            c = color_str(m[colors[i]].as_long())
            p = phone_str(m[phones[i]].as_long())
            o = occupation_str(m[occupations[i]].as_long())
            rows.append([house, n, c, p, o])
        
        # Create the solution dictionary
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Color", "PhoneModel", "Occupation"],
                "rows": rows
            }
        }
        
        # Output as JSON
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()