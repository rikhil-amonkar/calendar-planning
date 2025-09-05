from z3 import *
import json

def main():
    s = Solver()

    # Define variables for names, heights, and foods.
    names = {
        "Arnold": Int("Name_Arnold"),
        "Bob": Int("Name_Bob"),
        "Alice": Int("Name_Alice"),
        "Eric": Int("Name_Eric"),
        "Peter": Int("Name_Peter")
    }
    
    heights = {
        "very tall": Int("Height_very_tall"),
        "average": Int("Height_average"),
        "tall": Int("Height_tall"),
        "very short": Int("Height_very_short"),
        "short": Int("Height_short")
    }
    
    foods = {
        "stew": Int("Food_stew"),
        "grilled cheese": Int("Food_grilled_cheese"),
        "spaghetti": Int("Food_spaghetti"),
        "pizza": Int("Food_pizza"),
        "stir fry": Int("Food_stir_fry")
    }
    
    # Domain constraints: All positions are between 1 and 5.
    all_vars = list(names.values()) + list(heights.values()) + list(foods.values())
    for var in all_vars:
        s.add(var >= 1, var <= 5)
    
    # Each category uses distinct house positions.
    s.add(Distinct(list(names.values())))
    s.add(Distinct(list(heights.values())))
    s.add(Distinct(list(foods.values())))
    
    # Apply the clues:
    # 1. Alice is the person who is short.
    s.add(names["Alice"] == heights["short"])
    
    # 2. The person who is tall is in the third house.
    s.add(heights["tall"] == 3)
    
    # 3. The person who has an average height is not in the second house.
    s.add(heights["average"] != 2)
    
    # 4. The person who has an average height is somewhere to the left of the person who loves the stew.
    s.add(heights["average"] < foods["stew"])
    
    # 5. The person who loves stir fry is Arnold.
    s.add(foods["stir fry"] == names["Arnold"])
    
    # 6. The person who is a pizza lover is the person who is tall.
    s.add(foods["pizza"] == heights["tall"])
    
    # 7. Eric is the person who is tall.
    s.add(names["Eric"] == heights["tall"])
    
    # 8. Bob is somewhere to the right of Arnold.
    s.add(names["Bob"] > names["Arnold"])
    
    # 9. The person who loves eating grilled cheese is somewhere to the right of Eric.
    s.add(foods["grilled cheese"] > names["Eric"])
    
    # 10. The person who is very short is somewhere to the left of Arnold.
    s.add(heights["very short"] < names["Arnold"])
    
    if s.check() == sat:
        m = s.model()
        
        # Prepare a mapping from house number to its attributes.
        houses = {i: {"Name": None, "Height": None, "Food": None} for i in range(1, 6)}
        
        for name, var in names.items():
            pos = m.evaluate(var).as_long()
            houses[pos]["Name"] = name
        
        for height, var in heights.items():
            pos = m.evaluate(var).as_long()
            houses[pos]["Height"] = height
        
        for food, var in foods.items():
            pos = m.evaluate(var).as_long()
            houses[pos]["Food"] = food
        
        # Build rows in order of houses 1 to 5.
        rows = []
        for i in range(1, 6):
            row = [str(i), houses[i]["Name"], houses[i]["Height"], houses[i]["Food"]]
            rows.append(row)
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Height", "Food"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()