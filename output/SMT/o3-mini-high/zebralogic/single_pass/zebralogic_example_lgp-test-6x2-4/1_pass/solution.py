from z3 import *
import json

def solve_puzzle():
    # Define lists of persons and phone models
    persons = ["Alice", "Arnold", "Carol", "Peter", "Bob", "Eric"]
    phones  = ["huawei p50", "iphone 13", "xiaomi mi 11", "oneplus 9", "samsung galaxy s21", "google pixel 6"]

    # Create a Z3 integer variable for each person.
    # The variable represents the house number (1 through 6) where that person lives.
    person_house = {name: Int(f"house_{name}") for name in persons}
    # Create a Z3 integer variable for each phone model.
    # The variable represents the house number (1 through 6) where that phone is used.
    phone_house  = {phone: Int(f"phone_{phone.replace(' ', '_').replace('-', '_')}") for phone in phones}
    
    s = Solver()

    # Each house number is between 1 and 6.
    for var in person_house.values():
        s.add(var >= 1, var <= 6)
    for var in phone_house.values():
        s.add(var >= 1, var <= 6)
    
    # All persons live in different houses.
    s.add(Distinct(list(person_house.values())))
    # All phone models are used in different houses.
    s.add(Distinct(list(phone_house.values())))

    # --- Add the clues as constraints ---
    # 1. The person who uses an iPhone 13 is Alice.
    #    This means that wherever iPhone 13 is used, it must be by Alice.
    s.add(person_house["Alice"] == phone_house["iphone 13"])

    # 2. The person who uses a Huawei P50 is in the first house.
    s.add(phone_house["huawei p50"] == 1)

    # 3. The person who uses a OnePlus 9 is in the sixth house.
    s.add(phone_house["oneplus 9"] == 6)

    # 4. The person who uses a Google Pixel 6 is not in the second house.
    s.add(phone_house["google pixel 6"] != 2)

    # 5. The person who uses an iPhone 13 is not in the second house.
    s.add(phone_house["iphone 13"] != 2)

    # 6. There is one house between Bob and Carol.
    s.add(Abs(person_house["Bob"] - person_house["Carol"]) == 2)

    # 7. The person who uses a Huawei P50 is Eric.
    s.add(person_house["Eric"] == phone_house["huawei p50"])

    # 8. The person who uses a Xiaomi Mi 11 is in the third house.
    s.add(phone_house["xiaomi mi 11"] == 3)

    # 9. Alice is somewhere to the left of Carol.
    s.add(person_house["Alice"] < person_house["Carol"])

    # 10. Arnold is the person who uses a OnePlus 9.
    s.add(person_house["Arnold"] == phone_house["oneplus 9"])

    # --- Solve the model ---
    if s.check() == sat:
        m = s.model()
        # Build a mapping from house number to the person and phone model at that house.
        house_info = {}
        for name, var in person_house.items():
            hnum = m[var].as_long()
            house_info.setdefault(hnum, {})["Name"] = name
        for phone, var in phone_house.items():
            hnum = m[var].as_long()
            house_info.setdefault(hnum, {})["PhoneModel"] = phone
        
        # Prepare the output rows for houses numbered 1 to 6.
        rows = []
        for i in range(1, 7):
            # The house number is converted to a string.
            person_val = house_info.get(i, {}).get("Name", "")
            phone_val  = house_info.get(i, {}).get("PhoneModel", "")
            rows.append([str(i), person_val, phone_val])
        
        # Build the final solution dictionary in the required JSON structure.
        solution = {
            "solution": {
                "header": ["House", "Name", "PhoneModel"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    solve_puzzle()