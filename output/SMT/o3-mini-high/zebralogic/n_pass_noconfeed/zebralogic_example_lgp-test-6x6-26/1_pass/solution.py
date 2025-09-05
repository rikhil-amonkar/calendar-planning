from z3 import *
import json

def main():
    solver = Solver()

    # Define domains: every variable is an integer representing a house position (1 to 6).
    # Define variables for each attribute value.
    names = {
        "Peter": Int("Peter"),
        "Carol": Int("Carol"),
        "Eric": Int("Eric"),
        "Alice": Int("Alice"),
        "Bob": Int("Bob"),
        "Arnold": Int("Arnold")
    }
    phones = {
        "huawei p50": Int("huawei_p50"),
        "google pixel 6": Int("google_pixel_6"),
        "xiaomi mi 11": Int("xiaomi_mi_11"),
        "iphone 13": Int("iphone_13"),
        "samsung galaxy s21": Int("samsung_galaxy_s21"),
        "oneplus 9": Int("oneplus_9")
    }
    cigars = {
        "dunhill": Int("dunhill"),
        "pall mall": Int("pall_mall"),
        "blends": Int("blends"),
        "blue master": Int("blue_master"),
        "prince": Int("prince"),
        "yellow monster": Int("yellow_monster")
    }
    flowers = {
        "daffodils": Int("daffodils"),
        "carnations": Int("carnations"),
        "roses": Int("roses"),
        "tulips": Int("tulips"),
        "lilies": Int("lilies"),
        "iris": Int("iris")
    }
    colors = {
        "yellow": Int("yellow"),
        "red": Int("red"),
        "green": Int("green"),
        "blue": Int("blue"),
        "white": Int("white"),
        "purple": Int("purple")
    }
    sports = {
        "soccer": Int("soccer"),
        "tennis": Int("tennis"),
        "basketball": Int("basketball"),
        "volleyball": Int("volleyball"),
        "swimming": Int("swimming"),
        "baseball": Int("baseball")
    }

    # All variables must take values from 1 to 6.
    all_vars = list(names.values()) + list(phones.values()) + list(cigars.values()) + \
               list(flowers.values()) + list(colors.values()) + list(sports.values())
    for var in all_vars:
        solver.add(And(var >= 1, var <= 6))
    
    # Each category must have all different house positions.
    solver.add(Distinct(list(names.values())))
    solver.add(Distinct(list(phones.values())))
    solver.add(Distinct(list(cigars.values())))
    solver.add(Distinct(list(flowers.values())))
    solver.add(Distinct(list(colors.values())))
    solver.add(Distinct(list(sports.values())))
    
    # Add puzzle constraints based on the clues.
    # 1. The person who uses a OnePlus 9 is in the second house.
    solver.add(phones["oneplus 9"] == 2)
    
    # 2. The person who uses a Xiaomi Mi 11 is somewhere to the left of the person who uses a Huawei P50.
    solver.add(phones["xiaomi mi 11"] < phones["huawei p50"])
    
    # 3. Carol is the person who loves a carnations arrangement.
    solver.add(names["Carol"] == flowers["carnations"])
    
    # 4. The person who loves purple is directly left of the person partial to Pall Mall.
    solver.add(colors["purple"] == cigars["pall mall"] - 1)
    
    # 5. The person whose favorite color is green is the person who smokes Blue Master.
    solver.add(colors["green"] == cigars["blue master"])
    
    # 6. The person who loves yellow and the person who loves blue are next to each other.
    solver.add(Or(colors["yellow"] == colors["blue"] + 1, colors["yellow"] == colors["blue"] - 1))
    
    # 7. Eric is somewhere to the right of the person who uses a Samsung Galaxy S21.
    solver.add(names["Eric"] > phones["samsung galaxy s21"])
    
    # 8. There are two houses between Carol and the person who loves a bouquet of daffodils.
    solver.add(Abs(names["Carol"] - flowers["daffodils"]) == 3)
    
    # 9. The Prince smoker is the person who loves basketball.
    solver.add(cigars["prince"] == sports["basketball"])
    
    # 10. The Dunhill smoker is the person who loves volleyball.
    solver.add(cigars["dunhill"] == sports["volleyball"])
    
    # 11. The person who loves swimming is the person who uses a Google Pixel 6.
    solver.add(sports["swimming"] == phones["google pixel 6"])
    
    # 12. The person who uses a Huawei P50 is directly left of the person who loves white.
    solver.add(phones["huawei p50"] == colors["white"] - 1)
    
    # 13. The person who uses a OnePlus 9 and the person who loves the rose bouquet are next to each other.
    solver.add(Or(phones["oneplus 9"] == flowers["roses"] + 1, phones["oneplus 9"] == flowers["roses"] - 1))
    
    # 14. The person who loves the bouquet of iris is somewhere to the left of Eric.
    solver.add(flowers["iris"] < names["Eric"])
    
    # 15. The Dunhill smoker is Peter.
    solver.add(cigars["dunhill"] == names["Peter"])
    
    # 16. The person who loves blue is Peter.
    solver.add(colors["blue"] == names["Peter"])
    
    # 17. The person who loves the vase of tulips is Bob.
    solver.add(flowers["tulips"] == names["Bob"])
    
    # 18. Alice is in the first house.
    solver.add(names["Alice"] == 1)
    
    # 19. The person who loves baseball is directly left of the person who smokes Blue Master.
    solver.add(sports["baseball"] == cigars["blue master"] - 1)
    
    # 20. The person who uses a Google Pixel 6 is somewhere to the right of the person who smokes many unique blends.
    solver.add(phones["google pixel 6"] > cigars["blends"])
    
    # 21. The person who loves soccer is Carol.
    solver.add(sports["soccer"] == names["Carol"])
    
    # 22. The person who loves a carnations arrangement is directly left of the person who smokes many unique blends.
    solver.add(flowers["carnations"] == cigars["blends"] - 1)
    
    # 23. Eric is the person who smokes many unique blends.
    solver.add(names["Eric"] == cigars["blends"])
    
    # 24. The person who loves volleyball is the person who uses an iPhone 13.
    solver.add(sports["volleyball"] == phones["iphone 13"])
    
    # Check if the constraints are satisfiable and retrieve the model.
    if solver.check() == sat:
        model = solver.model()
        # Build the solution per house (houses numbered 1 to 6).
        # For each house we determine the attribute values by matching the house number.
        houses = {}
        for i in range(1, 7):
            house_name = next((name for name, var in names.items() if model[var].as_long() == i), None)
            house_phone = next((phone for phone, var in phones.items() if model[var].as_long() == i), None)
            house_cigar = next((cigar for cigar, var in cigars.items() if model[var].as_long() == i), None)
            house_flower = next((flower for flower, var in flowers.items() if model[var].as_long() == i), None)
            house_color = next((color for color, var in colors.items() if model[var].as_long() == i), None)
            house_sport = next((sport for sport, var in sports.items() if model[var].as_long() == i), None)
            houses[i] = [
                str(i),
                house_name,
                house_phone,
                house_cigar,
                house_flower,
                house_color,
                house_sport
            ]
        
        result = {
            "solution": {
                "header": ["House", "Name", "PhoneModel", "Cigar", "Flower", "Color", "FavoriteSport"],
                "rows": [houses[i] for i in range(1, 7)]
            }
        }
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()