from z3 import *
import json

def main():
    s = Solver()
    
    # Create variables for person names
    Carol = Int("Carol")
    Bob = Int("Bob")
    Alice = Int("Alice")
    Arnold = Int("Arnold")
    Eric = Int("Eric")
    Peter = Int("Peter")
    names = [("Carol", Carol), ("Bob", Bob), ("Alice", Alice), ("Arnold", Arnold), ("Eric", Eric), ("Peter", Peter)]
    
    # Create variables for phone models
    S21 = Int("S21")
    Pixel = Int("Pixel")
    iPhone = Int("iPhone")
    Huawei = Int("Huawei")
    OnePlus = Int("OnePlus")
    Xiaomi = Int("Xiaomi")
    phones = [
        ("samsung galaxy s21", S21),
        ("google pixel 6", Pixel),
        ("iphone 13", iPhone),
        ("huawei p50", Huawei),
        ("oneplus 9", OnePlus),
        ("xiaomi mi 11", Xiaomi)
    ]
    
    # Create variables for nationalities
    swede = Int("swede")
    chinese = Int("chinese")
    norwegian = Int("norwegian")
    dane = Int("dane")
    german = Int("german")
    brit = Int("brit")
    nationalities = [
        ("swede", swede),
        ("chinese", chinese),
        ("norwegian", norwegian),
        ("dane", dane),
        ("german", german),
        ("brit", brit)
    ]
    
    # Create variables for colors
    blue = Int("blue")
    red = Int("red")
    yellow = Int("yellow")
    green = Int("green")
    white = Int("white")
    purple = Int("purple")
    colors = [
        ("blue", blue),
        ("red", red),
        ("yellow", yellow),
        ("green", green),
        ("white", white),
        ("purple", purple)
    ]
    
    # Each attribute variable must be between 1 and 6.
    for category in [names, phones, nationalities, colors]:
        s.add(Distinct([var for (_, var) in category]))
        for (_, var) in category:
            s.add(And(var >= 1, var <= 6))
    
    # Clue 1: Carol is not in the third house.
    s.add(Carol != 3)
    
    # Clue 2: There is one house between the Dane and the British person.
    s.add(Abs(dane - brit) == 2)
    
    # Clue 3: Carol is the person whose favorite color is green.
    s.add(Carol == green)
    
    # Clue 4: Arnold is directly left of Alice.
    s.add(Arnold + 1 == Alice)
    
    # Clue 5: Alice is the German.
    s.add(Alice == german)
    
    # Clue 6: The person who uses a OnePlus 9 is the person who loves purple.
    s.add(OnePlus == purple)
    
    # Clue 7: The person who uses a Huawei P50 is not in the third house.
    s.add(Huawei != 3)
    
    # Clue 8: The person who uses a Samsung Galaxy S21 is in the fifth house.
    s.add(S21 == 5)
    
    # Clue 9: The person who loves white is somewhere to the right of the person whose favorite color is red.
    s.add(red < white)
    
    # Clue 10: The person who uses a Samsung Galaxy S21 is Bob.
    s.add(S21 == Bob)
    
    # Clue 11: The Dane is the person who loves yellow.
    s.add(dane == yellow)
    
    # Clue 12: The person who uses a Samsung Galaxy S21 is somewhere to the left of Peter.
    s.add(S21 < Peter)
    
    # Clue 13: The person who loves blue is Peter.
    s.add(blue == Peter)
    
    # Clue 14: Peter is the British person.
    s.add(Peter == brit)
    
    # Clue 15: The person who uses a Samsung Galaxy S21 is directly left of the person who uses an iPhone 13.
    s.add(S21 + 1 == iPhone)
    
    # Clue 16: The Norwegian is the person who loves purple.
    s.add(norwegian == purple)
    
    # Clue 17: The person who uses a Xiaomi Mi 11 is the Chinese.
    s.add(Xiaomi == chinese)
    
    # Solve the constraints.
    if s.check() == sat:
        m = s.model()
        # Build the solution rows for houses 1 to 6.
        solution_rows = []
        for house in range(1, 7):
            house_name = [name for (name, var) in names if m[var].as_long() == house][0]
            house_phone = [phone for (phone, var) in phones if m[var].as_long() == house][0]
            house_nat = [nat for (nat, var) in nationalities if m[var].as_long() == house][0]
            house_color = [col for (col, var) in colors if m[var].as_long() == house][0]
            solution_rows.append([str(house), house_name, house_phone, house_nat, house_color])
        
        output = {
            "solution": {
                "header": ["House", "Name", "PhoneModel", "Nationality", "Color"],
                "rows": solution_rows
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()