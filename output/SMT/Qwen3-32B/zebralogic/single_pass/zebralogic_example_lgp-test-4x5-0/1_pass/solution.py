import json
from z3 import *

# Define EnumSorts
Name, (Eric, Peter, Arnold, Alice) = EnumSort('Name', ['Eric', 'Peter', 'Arnold', 'Alice'])
Smoothie, (Dragonfruit, Cherry, Desert, Watermelon) = EnumSort('Smoothie', ['dragonfruit', 'cherry', 'desert', 'watermelon'])
Cigar, (BlueMaster, PallMall, Dunhill, Prince) = EnumSort('Cigar', ['blue master', 'pall mall', 'dunhill', 'prince'])
Height, (Tall, Average, Short, VeryShort) = EnumSort('Height', ['tall', 'average', 'short', 'very short'])
PhoneModel, (GooglePixel6, SamsungGalaxyS21, Iphone13, Oneplus9) = EnumSort('PhoneModel', ['google pixel 6', 'samsung galaxy s21', 'iphone 13', 'oneplus 9'])

s = Solver()

# Variables for each house (1-4)
name_1, name_2, name_3, name_4 = Consts('name_1 name_2 name_3 name_4', Name)
smoothie_1, smoothie_2, smoothie_3, smoothie_4 = Consts('smoothie_1 smoothie_2 smoothie_3 smoothie_4', Smoothie)
cigar_1, cigar_2, cigar_3, cigar_4 = Consts('cigar_1 cigar_2 cigar_3 cigar_4', Cigar)
height_1, height_2, height_3, height_4 = Consts('height_1 height_2 height_3 height_4', Height)
phone_1, phone_2, phone_3, phone_4 = Consts('phone_1 phone_2 phone_3 phone_4', PhoneModel)

# Add distinctness constraints
s.add(Distinct(name_1, name_2, name_3, name_4))
s.add(Distinct(smoothie_1, smoothie_2, smoothie_3, smoothie_4))
s.add(Distinct(cigar_1, cigar_2, cigar_3, cigar_4))
s.add(Distinct(height_1, height_2, height_3, height_4))
s.add(Distinct(phone_1, phone_2, phone_3, phone_4))

# Clue 1: Dragonfruit lover is Eric
s.add(Implies(smoothie_1 == Dragonfruit, name_1 == Eric))
s.add(Implies(smoothie_2 == Dragonfruit, name_2 == Eric))
s.add(Implies(smoothie_3 == Dragonfruit, name_3 == Eric))
s.add(Implies(smoothie_4 == Dragonfruit, name_4 == Eric))

# Clue 2: Dunhill smoker likes Cherry
s.add(Implies(cigar_1 == Dunhill, smoothie_1 == Cherry))
s.add(Implies(cigar_2 == Dunhill, smoothie_2 == Cherry))
s.add(Implies(cigar_3 == Dunhill, smoothie_3 == Cherry))
s.add(Implies(cigar_4 == Dunhill, smoothie_4 == Cherry))

# Clue 3: Samsung left of iPhone
s.add(Implies(phone_1 == SamsungGalaxyS21, phone_2 == Iphone13))
s.add(Implies(phone_2 == SamsungGalaxyS21, phone_3 == Iphone13))
s.add(Implies(phone_3 == SamsungGalaxyS21, phone_4 == Iphone13))

# Clue 4: Dunhill is to the right of very short
s.add(Or(
    And(height_1 == VeryShort, Or(cigar_2 == Dunhill, cigar_3 == Dunhill, cigar_4 == Dunhill)),
    And(height_2 == VeryShort, Or(cigar_3 == Dunhill, cigar_4 == Dunhill)),
    And(height_3 == VeryShort, cigar_4 == Dunhill)
))

# Clue 5: Watermelon after Desert
s.add(Or(
    And(smoothie_1 == Desert, Or(smoothie_2 == Watermelon, smoothie_3 == Watermelon, smoothie_4 == Watermelon)),
    And(smoothie_2 == Desert, Or(smoothie_3 == Watermelon, smoothie_4 == Watermelon)),
    And(smoothie_3 == Desert, smoothie_4 == Watermelon)
))

# Clue 6: Prince smoker uses OnePlus9
s.add(Implies(cigar_1 == Prince, phone_1 == Oneplus9))
s.add(Implies(cigar_2 == Prince, phone_2 == Oneplus9))
s.add(Implies(cigar_3 == Prince, phone_3 == Oneplus9))
s.add(Implies(cigar_4 == Prince, phone_4 == Oneplus9))

# Clue 7: Tall in house 3
s.add(height_3 == Tall)

# Clue 8: Very short uses iPhone13
s.add(Implies(height_1 == VeryShort, phone_1 == Iphone13))
s.add(Implies(height_2 == VeryShort, phone_2 == Iphone13))
s.add(Implies(height_3 == VeryShort, phone_3 == Iphone13))
s.add(Implies(height_4 == VeryShort, phone_4 == Iphone13))

# Clue 9: BlueMaster not in first house
s.add(cigar_1 != BlueMaster)

# Clue 10: Dunhill smoker is short
s.add(Implies(cigar_1 == Dunhill, height_1 == Short))
s.add(Implies(cigar_2 == Dunhill, height_2 == Short))
s.add(Implies(cigar_3 == Dunhill, height_3 == Short))
s.add(Implies(cigar_4 == Dunhill, height_4 == Short))

# Clue 11: Peter not in third house
s.add(name_3 != Peter)

# Clue 12: Arnold uses GooglePixel6
s.add(Implies(name_1 == Arnold, phone_1 == GooglePixel6))
s.add(Implies(name_2 == Arnold, phone_2 == GooglePixel6))
s.add(Implies(name_3 == Arnold, phone_3 == GooglePixel6))
s.add(Implies(name_4 == Arnold, phone_4 == GooglePixel6))

# Clue 13: Dragonfruit lover is PallMall smoker
s.add(Implies(smoothie_1 == Dragonfruit, cigar_1 == PallMall))
s.add(Implies(smoothie_2 == Dragonfruit, cigar_2 == PallMall))
s.add(Implies(smoothie_3 == Dragonfruit, cigar_3 == PallMall))
s.add(Implies(smoothie_4 == Dragonfruit, cigar_4 == PallMall))

# Check if the constraints are satisfiable
if s.check() == sat:
    m = s.model()
    names = [name_1, name_2, name_3, name_4]
    smoothies = [smoothie_1, smoothie_2, smoothie_3, smoothie_4]
    cigars = [cigar_1, cigar_2, cigar_3, cigar_4]
    heights = [height_1, height_2, height_3, height_4]
    phones = [phone_1, phone_2, phone_3, phone_4]
    
    rows = []
    for i in range(4):
        house_num = str(i + 1)
        name = m.evaluate(names[i]).decl().name()
        smoothie = m.evaluate(smoothies[i]).decl().name()
        cigar = m.evaluate(cigars[i]).decl().name()
        height = m.evaluate(heights[i]).decl().name()
        phone = m.evaluate(phones[i]).decl().name()
        rows.append([house_num, name, smoothie, cigar, height, phone])
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Cigar", "Height", "PhoneModel"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")