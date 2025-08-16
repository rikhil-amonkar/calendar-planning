import json
from z3 import *

def main():
    solver = Solver()

    # Create Z3 integer variables representing the house number (1 to 4) for each attribute value.
    # House numbers: 1 (leftmost) to 4 (rightmost)
    
    # Names
    names = {
        "Eric": Int("Eric"),
        "Peter": Int("Peter"),
        "Arnold": Int("Arnold"),
        "Alice": Int("Alice")
    }
    
    # Smoothies
    smoothies = {
        "dragonfruit": Int("dragonfruit"),
        "cherry": Int("cherry"),
        "desert": Int("desert"),
        "watermelon": Int("watermelon")
    }
    
    # Cigars
    cigars = {
        "blue master": Int("blue_master"),
        "pall mall": Int("pall_mall"),
        "dunhill": Int("dunhill"),
        "prince": Int("prince")
    }
    
    # Heights
    heights = {
        "tall": Int("tall"),
        "average": Int("average"),
        "short": Int("short"),
        "very short": Int("very_short")
    }
    
    # Phone Models
    phones = {
        "google pixel 6": Int("google_pixel6"),
        "samsung galaxy s21": Int("samsung_galaxy_s21"),
        "iphone 13": Int("iphone_13"),
        "oneplus 9": Int("oneplus_9")
    }
    
    # All variables must be in the domain 1..4
    all_vars = list(names.values()) + list(smoothies.values()) + list(cigars.values()) + list(heights.values()) + list(phones.values())
    for var in all_vars:
        solver.add(var >= 1, var <= 4)
    
    # Each attribute group must be a permutation (all-different)
    solver.add(Distinct(list(names.values())))
    solver.add(Distinct(list(smoothies.values())))
    solver.add(Distinct(list(cigars.values())))
    solver.add(Distinct(list(heights.values())))
    solver.add(Distinct(list(phones.values())))
    
    # Now add the clues as constraints:
    
    # 1. The Dragonfruit smoothie lover is Eric.
    solver.add(smoothies["dragonfruit"] == names["Eric"])
    
    # 13. The Dragonfruit smoothie lover is the person partial to Pall Mall.
    solver.add(smoothies["dragonfruit"] == cigars["pall mall"])
    
    # 2. The Dunhill smoker is the person who likes Cherry smoothies.
    solver.add(cigars["dunhill"] == smoothies["cherry"])
    
    # 3. The person who uses a Samsung Galaxy S21 is directly left of the person who uses an iPhone 13.
    # (i.e. the Samsung user's house number plus one equals the iPhone user's house number)
    solver.add(phones["samsung galaxy s21"] + 1 == phones["iphone 13"])
    
    # 4. The Dunhill smoker is somewhere to the right of the person who is very short.
    solver.add(cigars["dunhill"] > heights["very short"])
    
    # 5. The Watermelon smoothie lover is somewhere to the right of the Desert smoothie lover.
    solver.add(smoothies["watermelon"] > smoothies["desert"])
    
    # 6. The Prince smoker is the person who uses an OnePlus 9.
    solver.add(cigars["prince"] == phones["oneplus 9"])
    
    # 7. The person who is tall is in the third house.
    solver.add(heights["tall"] == 3)
    
    # 8. The person who is very short is the person who uses an iPhone 13.
    solver.add(heights["very short"] == phones["iphone 13"])
    
    # 9. The person who smokes Blue Master is not in the first house.
    solver.add(cigars["blue master"] != 1)
    
    # 10. The Dunhill smoker is the person who is short.
    solver.add(cigars["dunhill"] == heights["short"])
    
    # 11. Peter is not in the third house.
    solver.add(names["Peter"] != 3)
    
    # 12. Arnold is the person who uses a Google Pixel 6.
    solver.add(names["Arnold"] == phones["google pixel 6"])
    
    # Solve the constraints
    if solver.check() == sat:
        model = solver.model()
        
        # For each house number, find the unique attribute value (key) in each category that is assigned that house.
        def find_by_value(d, val):
            for key, var in d.items():
                if model.evaluate(var).as_long() == val:
                    return key
            return None
        
        rows = []
        for house in range(1, 5):
            row = [
                str(house),
                find_by_value(names, house),
                find_by_value(smoothies, house),
                find_by_value(cigars, house),
                find_by_value(heights, house),
                find_by_value(phones, house)
            ]
            rows.append(row)
        
        output = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "Cigar", "Height", "PhoneModel"],
                "rows": rows
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()