from z3 import *
import json

def main():
    solver = Solver()
    
    # Define persons (names)
    persons = ["Alice", "Eric", "Bob", "Peter", "Arnold", "Carol"]
    names = {person: Int(person) for person in persons}
    
    # Define heights
    # "very tall", "tall", "super tall", "average", "very short", "short"
    height_keys = ["very tall", "tall", "super tall", "average", "very short", "short"]
    # Use variable names without spaces
    heights = {h: Int(h.replace(" ", "_")) for h in height_keys}
    
    # Define phone models
    phone_keys = ["oneplus 9", "google pixel 6", "samsung galaxy s21", "iphone 13", "huawei p50", "xiaomi mi 11"]
    phones = {p: Int(p.replace(" ", "_")) for p in phone_keys}
    
    # Domain constraints for names, heights, and phones: they must be in 1..6.
    for var in list(names.values()) + list(heights.values()) + list(phones.values()):
        solver.add(var >= 1, var <= 6)
    
    # All-different constraints for each category.
    solver.add(Distinct(list(names.values())))
    solver.add(Distinct(list(heights.values())))
    solver.add(Distinct(list(phones.values())))
    
    # Clue 9: The person who is super tall is in the first house.
    solver.add(heights["super tall"] == 1)
    # Clue 12: The person who is short is in the sixth house.
    solver.add(heights["short"] == 6)
    
    # Clue 7: The person who uses a OnePlus 9 is directly left of the person who is short.
    # Hence, phone "oneplus 9" + 1 == house of "short"
    solver.add(phones["oneplus 9"] + 1 == heights["short"])
    # With house 6 for "short", this forces:
    solver.add(phones["oneplus 9"] == 5)
    
    # Clue 5: There is one house between the person who uses a Google Pixel 6 and the person who is short.
    solver.add(Abs(phones["google pixel 6"] - heights["short"]) == 2)
    # With heights["short"] == 6, this forces:
    solver.add(phones["google pixel 6"] == 4)
    
    # Clue 1: Bob is directly left of the person who is tall.
    solver.add(names["Bob"] + 1 == heights["tall"])
    # Clue 8: The person who is tall is Arnold.
    solver.add(names["Arnold"] == heights["tall"])
    # Combined, these imply: names["Bob"] + 1 == names["Arnold"]
    
    # Clue 2: Peter is somewhere to the left of the person who uses an iPhone 13.
    solver.add(names["Peter"] < phones["iphone 13"])
    
    # Clue 3: The person who is very short is somewhere to the right of the person who uses a Google Pixel 6.
    solver.add(heights["very short"] > phones["google pixel 6"])
    
    # Clue 4: Carol is the person who is very tall.
    solver.add(names["Carol"] == heights["very tall"])
    
    # Clue 6: The person who uses a Samsung Galaxy S21 is not in the first house.
    solver.add(phones["samsung galaxy s21"] != 1)
    
    # Clue 10: The person who uses a Xiaomi Mi 11 is Carol.
    solver.add(phones["xiaomi mi 11"] == names["Carol"])
    
    # Clue 11: The person who uses a Google Pixel 6 is somewhere to the right of Eric.
    solver.add(names["Eric"] < phones["google pixel 6"])
    
    # Solve the puzzle.
    if solver.check() == sat:
        model = solver.model()
        # Build a mapping from house number to attributes.
        # For each house 1..6, find the person, height and phone that are assigned that number.
        solution = {
            "solution": {
                "header": ["House", "Name", "Height", "PhoneModel"],
                "rows": []
            }
        }
        
        for house in range(1, 7):
            # Determine the person for this house.
            person_name = None
            for p, var in names.items():
                if model.evaluate(var).as_long() == house:
                    person_name = p
                    break
            
            # Determine the height for this house.
            house_height = None
            for h, var in heights.items():
                if model.evaluate(var).as_long() == house:
                    house_height = h
                    break
            
            # Determine the phone model for this house.
            house_phone = None
            for ph, var in phones.items():
                if model.evaluate(var).as_long() == house:
                    house_phone = ph
                    break
            
            solution["solution"]["rows"].append([str(house), person_name, house_height, house_phone])
        
        print(json.dumps(solution))
    else:
        print(json.dumps({"solution": "No solution found"}))

if __name__ == "__main__":
    main()