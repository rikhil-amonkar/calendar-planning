from z3 import Solver, Int, Distinct, Or, Abs, sat
import json

def main():
    s = Solver()
    
    # Create integer variables representing the house number (1 to 5)
    # For Names
    bob = Int('bob')
    eric = Int('eric')
    arnold = Int('arnold')
    alice = Int('alice')
    peter = Int('peter')
    names = [bob, eric, arnold, alice, peter]
    
    # For Colors
    blue = Int('blue')
    green = Int('green')
    white = Int('white')
    yellow = Int('yellow')
    red = Int('red')
    colors = [blue, green, white, yellow, red]
    
    # For Phone Models
    huawei = Int('huawei')
    samsung = Int('samsung')      # samsung galaxy s21
    oneplus = Int('oneplus')      # oneplus 9
    iphone = Int('iphone')        # iphone 13
    google = Int('google')        # google pixel 6
    phones = [huawei, samsung, oneplus, iphone, google]
    
    # For Occupations
    artist = Int('artist')
    teacher = Int('teacher')
    doctor = Int('doctor')
    engineer = Int('engineer')
    lawyer = Int('lawyer')
    occupations = [artist, teacher, doctor, engineer, lawyer]
    
    # Each variable must be in the range 1..5.
    for var in names + colors + phones + occupations:
        s.add(var >= 1, var <= 5)
    
    # All items within each category must be in different houses.
    s.add(Distinct(bob, eric, arnold, alice, peter))
    s.add(Distinct(blue, green, white, yellow, red))
    s.add(Distinct(huawei, samsung, oneplus, iphone, google))
    s.add(Distinct(artist, teacher, doctor, engineer, lawyer))
    
    # Clue 2: Bob is in the second house.
    s.add(bob == 2)
    
    # Clue 3: The person who uses a Samsung Galaxy S21 is the person who is a doctor.
    s.add(samsung == doctor)
    
    # Clue 4: The person who is a doctor is the person who loves blue.
    s.add(doctor == blue)
    
    # Clue 7: The person who loves blue is directly left of the person whose favorite color is red.
    s.add(red == blue + 1)
    
    # Clue 6: The person who is a lawyer is the person who uses a OnePlus 9.
    s.add(lawyer == oneplus)
    
    # Clue 8: The person who is a lawyer is somewhere to the right of the person who uses a Samsung Galaxy S21.
    s.add(lawyer > samsung)
    
    # Clue 1: The person who is an engineer is somewhere to the right of the person who is a lawyer.
    s.add(engineer > lawyer)
    
    # Clue 9: There is one house between the person who uses a Google Pixel 6 and the person who uses a Huawei P50.
    s.add(Or(google == huawei + 2, huawei == google + 2))
    
    # Clue 10: Arnold is the person who is an engineer.
    s.add(arnold == engineer)
    
    # Clue 11: Alice is the person who loves yellow.
    s.add(alice == yellow)
    
    # Clue 12: The person who uses a Google Pixel 6 is Eric.
    s.add(eric == google)
    
    # Clue 13: The person who uses a Google Pixel 6 is the person who is a teacher.
    s.add(google == teacher)
    
    # Clue 14: The person whose favorite color is red is somewhere to the right of the person who is a teacher.
    s.add(red > teacher)
    
    # Clue 5: The person whose favorite color is green is not in the fifth house.
    s.add(green != 5)
    
    # Check if the system is satisfiable.
    if s.check() == sat:
        m = s.model()
        
        # Prepare a mapping from house number to its attributes.
        houses = {i: {"Name": "", "Color": "", "PhoneModel": "", "Occupation": ""} for i in range(1, 6)}
        
        # Map each Name variable to its house.
        if m.evaluate(bob).as_long() in houses:
            houses[m.evaluate(bob).as_long()]["Name"] = "Bob"
        if m.evaluate(eric).as_long() in houses:
            houses[m.evaluate(eric).as_long()]["Name"] = "Eric"
        if m.evaluate(arnold).as_long() in houses:
            houses[m.evaluate(arnold).as_long()]["Name"] = "Arnold"
        if m.evaluate(alice).as_long() in houses:
            houses[m.evaluate(alice).as_long()]["Name"] = "Alice"
        if m.evaluate(peter).as_long() in houses:
            houses[m.evaluate(peter).as_long()]["Name"] = "Peter"
        
        # Map each Color variable.
        if m.evaluate(blue).as_long() in houses:
            houses[m.evaluate(blue).as_long()]["Color"] = "blue"
        if m.evaluate(green).as_long() in houses:
            houses[m.evaluate(green).as_long()]["Color"] = "green"
        if m.evaluate(white).as_long() in houses:
            houses[m.evaluate(white).as_long()]["Color"] = "white"
        if m.evaluate(yellow).as_long() in houses:
            houses[m.evaluate(yellow).as_long()]["Color"] = "yellow"
        if m.evaluate(red).as_long() in houses:
            houses[m.evaluate(red).as_long()]["Color"] = "red"
        
        # Map each Phone Model variable.
        if m.evaluate(huawei).as_long() in houses:
            houses[m.evaluate(huawei).as_long()]["PhoneModel"] = "huawei p50"
        if m.evaluate(samsung).as_long() in houses:
            houses[m.evaluate(samsung).as_long()]["PhoneModel"] = "samsung galaxy s21"
        if m.evaluate(oneplus).as_long() in houses:
            houses[m.evaluate(oneplus).as_long()]["PhoneModel"] = "oneplus 9"
        if m.evaluate(iphone).as_long() in houses:
            houses[m.evaluate(iphone).as_long()]["PhoneModel"] = "iphone 13"
        if m.evaluate(google).as_long() in houses:
            houses[m.evaluate(google).as_long()]["PhoneModel"] = "google pixel 6"
        
        # Map each Occupation variable.
        if m.evaluate(artist).as_long() in houses:
            houses[m.evaluate(artist).as_long()]["Occupation"] = "artist"
        if m.evaluate(teacher).as_long() in houses:
            houses[m.evaluate(teacher).as_long()]["Occupation"] = "teacher"
        if m.evaluate(doctor).as_long() in houses:
            houses[m.evaluate(doctor).as_long()]["Occupation"] = "doctor"
        if m.evaluate(engineer).as_long() in houses:
            houses[m.evaluate(engineer).as_long()]["Occupation"] = "engineer"
        if m.evaluate(lawyer).as_long() in houses:
            houses[m.evaluate(lawyer).as_long()]["Occupation"] = "lawyer"
        
        # Build the rows in the order of the houses 1 through 5.
        rows = []
        for i in range(1, 6):
            row = [
                str(i),
                houses[i]["Name"],
                houses[i]["Color"],
                houses[i]["PhoneModel"],
                houses[i]["Occupation"]
            ]
            rows.append(row)
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Color", "PhoneModel", "Occupation"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == '__main__':
    main()