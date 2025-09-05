from z3 import *
import json

def main():
    s = Solver()
    
    # Define variables for each attribute as integers representing house positions (1 to 5)
    names = {
        "Peter": Int("Peter"),
        "Arnold": Int("Arnold"),
        "Eric": Int("Eric"),
        "Bob": Int("Bob"),
        "Alice": Int("Alice")
    }
    heights = {
        "average": Int("average_height"),
        "very tall": Int("very_tall"),
        "very short": Int("very_short"),
        "short": Int("short_height"),
        "tall": Int("tall")
    }
    cigars = {
        "prince": Int("prince"),
        "dunhill": Int("dunhill"),
        "blends": Int("blends"),
        "pall mall": Int("pall_mall"),
        "blue master": Int("blue_master")
    }
    smoothies = {
        "lime": Int("lime"),
        "cherry": Int("cherry"),
        "dragonfruit": Int("dragonfruit"),
        "watermelon": Int("watermelon"),
        "desert": Int("desert")
    }
    phones = {
        "oneplus 9": Int("oneplus9"),
        "samsung galaxy s21": Int("samsung"),
        "iphone 13": Int("iphone13"),
        "huawei p50": Int("huawei"),
        "google pixel 6": Int("google")
    }
    
    # Domain constraints: each variable must be between 1 and 5 (houses 1 to 5)
    all_vars = list(names.values()) + list(heights.values()) + list(cigars.values()) + list(smoothies.values()) + list(phones.values())
    for var in all_vars:
        s.add(var >= 1, var <= 5)
    
    # All-different constraints for each attribute set
    s.add(Distinct(list(names.values())))
    s.add(Distinct(list(heights.values())))
    s.add(Distinct(list(cigars.values())))
    s.add(Distinct(list(smoothies.values())))
    s.add(Distinct(list(phones.values())))
    
    # Apply the clues as constraints:
    # 1. The Prince smoker is the Desert smoothie lover.
    s.add(cigars["prince"] == smoothies["desert"])
    
    # 2. There is one house between Eric and Alice.
    s.add(Abs(names["Eric"] - names["Alice"]) == 2)
    
    # 3. The person who is short is the person who smokes Blends.
    s.add(heights["short"] == cigars["blends"])
    
    # 4. The person who uses an iPhone 13 is directly left of the person who smokes Blue Master.
    s.add(phones["iphone 13"] + 1 == cigars["blue master"])
    
    # 5. The person who has an average height is the Dunhill smoker.
    s.add(heights["average"] == cigars["dunhill"])
    
    # 6. Eric is the person who is very tall.
    s.add(names["Eric"] == heights["very tall"])
    
    # 7. Arnold is directly left of the person who uses a Huawei P50.
    s.add(names["Arnold"] + 1 == phones["huawei p50"])
    
    # 8. Bob is not in the fourth house.
    s.add(names["Bob"] != 4)
    
    # 9. Eric is directly left of the person who likes Cherry smoothies.
    s.add(names["Eric"] + 1 == smoothies["cherry"])
    
    # 10. Bob is the Dunhill smoker.
    s.add(names["Bob"] == cigars["dunhill"])
    
    # 11. The Dragonfruit smoothie lover is Bob.
    s.add(smoothies["dragonfruit"] == names["Bob"])
    
    # 12. The person who uses an iPhone 13 and the person who uses a OnePlus 9 are next to each other.
    s.add(Abs(phones["iphone 13"] - phones["oneplus 9"]) == 1)
    
    # 13. The person who uses a Samsung Galaxy S21 is the person who is short.
    s.add(phones["samsung galaxy s21"] == heights["short"])
    
    # 14. There are two houses between the person who is very tall and the Dragonfruit smoothie lover.
    s.add(Abs(heights["very tall"] - smoothies["dragonfruit"]) == 3)
    
    # 15. The person who uses an iPhone 13 is Eric.
    s.add(phones["iphone 13"] == names["Eric"])
    
    # 16. The Desert smoothie lover is somewhere to the left of the person who drinks Lime smoothies.
    s.add(smoothies["desert"] < smoothies["lime"])
    
    # 17. Arnold and the person who is very short are next to each other.
    s.add(Abs(names["Arnold"] - heights["very short"]) == 1)
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        
        # Build inverse mapping: house number -> attribute value for each category.
        house_names = {}
        for key, var in names.items():
            pos = m[var].as_long()
            house_names[pos] = key
        house_heights = {}
        for key, var in heights.items():
            pos = m[var].as_long()
            house_heights[pos] = key
        house_cigars = {}
        for key, var in cigars.items():
            pos = m[var].as_long()
            house_cigars[pos] = key
        house_smoothies = {}
        for key, var in smoothies.items():
            pos = m[var].as_long()
            house_smoothies[pos] = key
        house_phones = {}
        for key, var in phones.items():
            pos = m[var].as_long()
            house_phones[pos] = key
        
        # Prepare the rows in the order of houses 1 to 5
        rows = []
        for i in range(1, 6):
            row = [
                str(i),
                house_names.get(i, ""),
                house_heights.get(i, ""),
                house_cigars.get(i, ""),
                house_smoothies.get(i, ""),
                house_phones.get(i, "")
            ]
            rows.append(row)
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Height", "Cigar", "Smoothie", "PhoneModel"],
                "rows": rows
            }
        }
        print(json.dumps(solution))
    else:
        print(json.dumps({"solution": None}))

if __name__ == '__main__':
    main()