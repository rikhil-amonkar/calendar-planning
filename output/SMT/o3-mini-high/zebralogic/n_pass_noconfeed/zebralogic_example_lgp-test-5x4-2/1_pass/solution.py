from z3 import *
import json

def main():
    s = Solver()
    
    # Define variables for names (each represents the house number 1..5)
    bob = Int('bob')
    eric = Int('eric')
    arnold = Int('arnold')
    alice = Int('alice')
    peter = Int('peter')
    names = [bob, eric, arnold, alice, peter]
    
    # Define variables for favorite colors
    color_blue = Int('color_blue')
    color_green = Int('color_green')
    color_white = Int('color_white')
    color_yellow = Int('color_yellow')
    color_red = Int('color_red')
    colors = [color_blue, color_green, color_white, color_yellow, color_red]
    
    # Define variables for phone models
    phone_huawei = Int('phone_huawei')
    phone_samsung = Int('phone_samsung')
    phone_oneplus = Int('phone_oneplus')
    phone_iphone = Int('phone_iphone')
    phone_google = Int('phone_google')
    phones = [phone_huawei, phone_samsung, phone_oneplus, phone_iphone, phone_google]
    
    # Define variables for occupations
    occ_artist = Int('occ_artist')
    occ_teacher = Int('occ_teacher')
    occ_doctor = Int('occ_doctor')
    occ_engineer = Int('occ_engineer')
    occ_lawyer = Int('occ_lawyer')
    occupations = [occ_artist, occ_teacher, occ_doctor, occ_engineer, occ_lawyer]
    
    # All variables must be in the range 1 to 5
    for var in names + colors + phones + occupations:
        s.add(And(var >= 1, var <= 5))
        
    # Each attribute must be assigned to a unique house.
    s.add(Distinct(names))
    s.add(Distinct(colors))
    s.add(Distinct(phones))
    s.add(Distinct(occupations))
    
    # Puzzle Clues:
    # 2. Bob is in the second house.
    s.add(bob == 2)
    
    # 3. The person who uses a Samsung Galaxy S21 is the person who is a doctor.
    s.add(phone_samsung == occ_doctor)
    
    # 4. The person who is a doctor is the person who loves blue.
    s.add(occ_doctor == color_blue)
    
    # 5. The person whose favorite color is green is not in the fifth house.
    s.add(color_green != 5)
    
    # 6. The person who is a lawyer is the person who uses a OnePlus 9.
    s.add(occ_lawyer == phone_oneplus)
    
    # 7. The person who loves blue is directly left of the person whose favorite color is red.
    s.add(color_blue + 1 == color_red)
    
    # 8. The person who is a lawyer is somewhere to the right of the person who uses a Samsung Galaxy S21.
    s.add(occ_lawyer > phone_samsung)
    
    # 9. There is one house between the person who uses a Google Pixel 6 and the person who uses a Huawei P50.
    s.add(Or(phone_google - phone_huawei == 2, phone_huawei - phone_google == 2))
    
    # 10. Arnold is the person who is an engineer.
    s.add(arnold == occ_engineer)
    
    # 11. Alice is the person who loves yellow.
    s.add(alice == color_yellow)
    
    # 12. The person who uses a Google Pixel 6 is Eric.
    s.add(phone_google == eric)
    
    # 13. The person who uses a Google Pixel 6 is the person who is a teacher.
    s.add(phone_google == occ_teacher)
    
    # 14. The person whose favorite color is red is somewhere to the right of the person who is a teacher.
    s.add(color_red > occ_teacher)
    
    # 1. The person who is an engineer is somewhere to the right of the person who is a lawyer.
    s.add(occ_engineer > occ_lawyer)
    
    # Solve the puzzle
    if s.check() == sat:
        m = s.model()
        
        # Build mappings from house number to the corresponding attribute for each category.
        names_mapping = {}
        for name, var in [("Bob", bob), ("Eric", eric), ("Arnold", arnold), ("Alice", alice), ("Peter", peter)]:
            names_mapping[m[var].as_long()] = name

        colors_mapping = {}
        for col, var in [("blue", color_blue), ("green", color_green), ("white", color_white), ("yellow", color_yellow), ("red", color_red)]:
            colors_mapping[m[var].as_long()] = col

        phones_mapping = {}
        for ph, var in [("huawei p50", phone_huawei), ("samsung galaxy s21", phone_samsung), ("oneplus 9", phone_oneplus), ("iphone 13", phone_iphone), ("google pixel 6", phone_google)]:
            phones_mapping[m[var].as_long()] = ph

        occupations_mapping = {}
        for occ, var in [("artist", occ_artist), ("teacher", occ_teacher), ("doctor", occ_doctor), ("engineer", occ_engineer), ("lawyer", occ_lawyer)]:
            occupations_mapping[m[var].as_long()] = occ

        # Assemble the solution rows in house order 1 to 5
        rows = []
        for house in range(1, 6):
            row = [
                str(house),
                names_mapping[house],
                colors_mapping[house],
                phones_mapping[house],
                occupations_mapping[house]
            ]
            rows.append(row)
        
        result = {
            "solution": {
                "header": ["House", "Name", "Color", "PhoneModel", "Occupation"],
                "rows": rows
            }
        }
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"solution": {}}))

if __name__ == "__main__":
    main()