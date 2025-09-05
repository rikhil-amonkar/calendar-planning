import json
from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Define attribute values
    names = ["Peter", "Carol", "Eric", "Alice", "Bob", "Arnold"]
    phones = ["huawei p50", "google pixel 6", "xiaomi mi 11", "iphone 13", "samsung galaxy s21", "oneplus 9"]
    cigars = ["dunhill", "pall mall", "blends", "blue master", "prince", "yellow monster"]
    flowers = ["daffodils", "carnations", "roses", "tulips", "lilies", "iris"]
    colors = ["yellow", "red", "green", "blue", "white", "purple"]
    sports = ["soccer", "tennis", "basketball", "volleyball", "swimming", "baseball"]
    
    # Create house position variables for each attribute value
    name_house = {n: Int(f"{n}_house") for n in names}
    phone_house = {p: Int(f"{p.replace(' ', '_')}_house") for p in phones}
    cigar_house = {c: Int(f"{c.replace(' ', '_')}_house") for c in cigars}
    flower_house = {f: Int(f"{f}_house") for f in flowers}
    color_house = {c: Int(f"{c}_house") for c in colors}
    sport_house = {s: Int(f"{s}_house") for s in sports}
    
    # All house positions must be between 1 and 6
    for var_dict in [name_house, phone_house, cigar_house, flower_house, color_house, sport_house]:
        for var in var_dict.values():
            s.add(var >= 1, var <= 6)
    
    # Each attribute type has distinct house values
    s.add(Distinct([v for v in name_house.values()]))
    s.add(Distinct([v for v in phone_house.values()]))
    s.add(Distinct([v for v in cigar_house.values()]))
    s.add(Distinct([v for v in flower_house.values()]))
    s.add(Distinct([v for v in color_house.values()]))
    s.add(Distinct([v for v in sport_house.values()]))
    
    # Add constraints from clues
    # 1. OnePlus 9 in second house
    s.add(phone_house["oneplus 9"] == 2)
    
    # 2. Xiaomi Mi 11 left of Huawei P50
    s.add(phone_house["xiaomi mi 11"] < phone_house["huawei p50"])
    
    # 3. Carol loves carnations
    s.add(name_house["Carol"] == flower_house["carnations"])
    
    # 4. Purple left of Pall Mall
    s.add(color_house["purple"] == cigar_house["pall mall"] - 1)
    
    # 5. Green color smokes Blue Master
    s.add(color_house["green"] == cigar_house["blue master"])
    
    # 6. Yellow and blue colors adjacent
    yellow, blue = color_house["yellow"], color_house["blue"]
    s.add(Or(yellow == blue - 1, yellow == blue + 1))
    
    # 7. Eric right of Samsung Galaxy S21 user
    s.add(name_house["Eric"] > phone_house["samsung galaxy s21"])
    
    # 8. Two houses between Carol and daffodils
    carol, daffodils = name_house["Carol"], flower_house["daffodils"]
    s.add(Or(carol == daffodils - 3, carol == daffodils + 3))
    
    # 9. Prince smoker loves basketball
    s.add(cigar_house["prince"] == sport_house["basketball"])
    
    # 10. Dunhill smoker loves volleyball
    s.add(cigar_house["dunhill"] == sport_house["volleyball"])
    
    # 11. Swimming lover uses Google Pixel 6
    s.add(sport_house["swimming"] == phone_house["google pixel 6"])
    
    # 12. Huawei P50 left of white color
    s.add(phone_house["huawei p50"] == color_house["white"] - 1)
    
    # 13. OnePlus 9 and roses adjacent
    op9, roses = phone_house["oneplus 9"], flower_house["roses"]
    s.add(Or(op9 == roses - 1, op9 == roses + 1))
    
    # 14. Iris left of Eric
    s.add(flower_house["iris"] < name_house["Eric"])
    
    # 15. Dunhill smoker is Peter
    s.add(cigar_house["dunhill"] == name_house["Peter"])
    
    # 16. Peter loves blue color
    s.add(color_house["blue"] == name_house["Peter"])
    
    # 17. Bob loves tulips
    s.add(name_house["Bob"] == flower_house["tulips"])
    
    # 18. Alice in first house
    s.add(name_house["Alice"] == 1)
    
    # 19. Baseball left of Blue Master smoker
    s.add(sport_house["baseball"] == cigar_house["blue master"] - 1)
    
    # 20. Google Pixel 6 right of blends smoker
    s.add(phone_house["google pixel 6"] > cigar_house["blends"])
    
    # 21. Carol loves soccer
    s.add(name_house["Carol"] == sport_house["soccer"])
    
    # 22. Carnations left of blends
    s.add(flower_house["carnations"] == cigar_house["blends"] - 1)
    
    # 23. Eric smokes blends
    s.add(name_house["Eric"] == cigar_house["blends"])
    
    # 24. Volleyball lover uses iPhone 13
    s.add(sport_house["volleyball"] == phone_house["iphone 13"])
    
    # Check solution
    if s.check() == sat:
        m = s.model()
        
        # Create solution table
        header = ["House", "Name", "PhoneModel", "Cigar", "Flower", "Color", "FavoriteSport"]
        rows = []
        
        for house in range(1, 7):
            row = [str(house)]
            # Find name for this house
            for name, var in name_house.items():
                if m.evaluate(var).as_long() == house:
                    row.append(name)
                    break
            # Find phone for this house
            for phone, var in phone_house.items():
                if m.evaluate(var).as_long() == house:
                    row.append(phone)
                    break
            # Find cigar for this house
            for cigar, var in cigar_house.items():
                if m.evaluate(var).as_long() == house:
                    row.append(cigar)
                    break
            # Find flower for this house
            for flower, var in flower_house.items():
                if m.evaluate(var).as_long() == house:
                    row.append(flower)
                    break
            # Find color for this house
            for color, var in color_house.items():
                if m.evaluate(var).as_long() == house:
                    row.append(color)
                    break
            # Find sport for this house
            for sport, var in sport_house.items():
                if m.evaluate(var).as_long() == house:
                    row.append(sport)
                    break
            rows.append(row)
        
        # Create JSON output
        solution = {
            "solution": {
                "header": header,
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()