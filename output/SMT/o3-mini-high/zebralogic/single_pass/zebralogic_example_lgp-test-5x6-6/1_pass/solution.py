from z3 import *
import json

def main():
    s = Solver()
    houses = [1,2,3,4,5]

    # Create a Z3 Int variable for each attribute item.
    # Names (each variable represents the house number in which that person lives):
    name = {
        "Arnold": Int("name_Arnold"),
        "Eric": Int("name_Eric"),
        "Alice": Int("name_Alice"),
        "Bob": Int("name_Bob"),
        "Peter": Int("name_Peter")
    }
    # Vacations:
    vacation = {
        "mountain": Int("vacation_mountain"),
        "city": Int("vacation_city"),
        "cruise": Int("vacation_cruise"),
        "beach": Int("vacation_beach"),
        "camping": Int("vacation_camping")
    }
    # Educations:
    edu = {
        "doctorate": Int("edu_doctorate"),
        "high school": Int("edu_high_school"),
        "bachelor": Int("edu_bachelor"),
        "associate": Int("edu_associate"),
        "master": Int("edu_master")
    }
    # Colors:
    color = {
        "blue": Int("color_blue"),
        "red": Int("color_red"),
        "white": Int("color_white"),
        "yellow": Int("color_yellow"),
        "green": Int("color_green")
    }
    # Phone models:
    phone = {
        "google pixel 6": Int("phone_google_pixel6"),
        "iphone 13": Int("phone_iphone_13"),
        "oneplus 9": Int("phone_oneplus_9"),
        "huawei p50": Int("phone_huawei_p50"),
        "samsung galaxy s21": Int("phone_samsung_galaxy_s21")
    }
    # Foods:
    food = {
        "grilled cheese": Int("food_grilled_cheese"),
        "stir fry": Int("food_stir_fry"),
        "pizza": Int("food_pizza"),
        "spaghetti": Int("food_spaghetti"),
        "stew": Int("food_stew")
    }

    # Each variable represents a house number between 1 and 5.
    def add_domain(d):
        for v in d.values():
            s.add(And(v >= 1, v <= 5))
    for d in [name, vacation, edu, color, phone, food]:
        add_domain(d)

    # All items in each category occupy different houses.
    s.add(Distinct(list(name.values())))
    s.add(Distinct(list(vacation.values())))
    s.add(Distinct(list(edu.values())))
    s.add(Distinct(list(color.values())))
    s.add(Distinct(list(phone.values())))
    s.add(Distinct(list(food.values())))

    # ----------------------------
    # Add the clues as constraints:
    #
    # 1. The person who loves the stew is not in the first house.
    s.add(food["stew"] != 1)
    # 2. There are two houses between the person who loves stir fry and the person with an associate's degree.
    s.add(Abs(food["stir fry"] - edu["associate"]) == 3)
    # 3. The person who enjoys mountain retreats is the person with a bachelor's degree.
    s.add(vacation["mountain"] == edu["bachelor"])
    # 4. The person with a doctorate is somewhere to the right of Bob.
    s.add(edu["doctorate"] > name["Bob"])
    # 5. The person who uses a Samsung Galaxy S21 is in the third house.
    s.add(phone["samsung galaxy s21"] == 3)
    # 6. Eric is the person with a doctorate.
    s.add(name["Eric"] == edu["doctorate"])
    # 7. The person with a doctorate is in the third house.
    s.add(edu["doctorate"] == 3)
    # 8. The person who loves stir fry is the person with a bachelor's degree.
    s.add(food["stir fry"] == edu["bachelor"])
    # 9. The person with a doctorate is the person who is a pizza lover.
    s.add(food["pizza"] == edu["doctorate"])
    # 10. The person whose favorite color is green is somewhere to the right of Peter.
    s.add(color["green"] > name["Peter"])
    # 11. The person who enjoys camping trips is the person who uses an iPhone 13.
    s.add(vacation["camping"] == phone["iphone 13"])
    # 12. The person who likes going on cruises is Alice.
    s.add(vacation["cruise"] == name["Alice"])
    # 13. There is one house between the person with a high school diploma and the person who uses a Samsung Galaxy S21.
    s.add(Abs(edu["high school"] - phone["samsung galaxy s21"]) == 2)
    # 14. The person who uses a Google Pixel 6 is Arnold.
    s.add(phone["google pixel 6"] == name["Arnold"])
    # 15. The person who uses a OnePlus 9 is somewhere to the right of the person who uses a Huawei P50.
    s.add(phone["oneplus 9"] > phone["huawei p50"])
    # 16. Arnold is the person who loves eating grilled cheese.
    s.add(food["grilled cheese"] == name["Arnold"])
    # 17. The person who loves eating grilled cheese is not in the fourth house.
    s.add(food["grilled cheese"] != 4)
    # 18. There are two houses between the person with a bachelor's degree and the person whose favorite color is red.
    s.add(Abs(edu["bachelor"] - color["red"]) == 3)
    # 19. The person who loves beach vacations is somewhere to the right of the person who prefers city breaks.
    s.add(vacation["beach"] > vacation["city"])
    # 20. The person whose favorite color is green is not in the second house.
    s.add(color["green"] != 2)
    # 21. The person who loves blue is somewhere to the right of Peter.
    s.add(color["blue"] > name["Peter"])
    # 22. There is one house between the person who enjoys camping trips and the person who loves yellow.
    s.add(Abs(vacation["camping"] - color["yellow"]) == 2)

    # ----------------------------
    # Additional (numeric) deductions:
    # From clues 5,6,7: Doctorate = 3 and Eric = 3.
    # From clue 11: vacation camping equals phone iphone 13.
    # In our search the only way to resolve the intersection (since the remaining possible numbers in phone set already used 
    # for others forces a unique match) is to set:
    s.add(phone["iphone 13"] == 1)
    s.add(vacation["camping"] == 1)
    # (This is a consequence of the interlocking of the available digits.)

    # ----------------------------
    # Now solve.
    if s.check() == sat:
        m = s.model()
        # Invert each category mapping (find which attribute gets a given house number):
        def invert(mapping):
            inv = {}
            for key, var in mapping.items():
                inv[m.evaluate(var).as_long()] = key
            return inv

        name_inv = invert(name)
        vacation_inv = invert(vacation)
        edu_inv = invert(edu)
        color_inv = invert(color)
        phone_inv = invert(phone)
        food_inv = invert(food)

        # Build rows for houses 1 through 5 (house numbers are strings as required):
        rows = []
        for h in range(1, 6):
            row = [
                str(h),
                name_inv.get(h, ""),
                vacation_inv.get(h, ""),
                edu_inv.get(h, ""),
                color_inv.get(h, ""),
                phone_inv.get(h, ""),
                food_inv.get(h, "")
            ]
            rows.append(row)

        solution = {
            "solution": {
                "header": ["House", "Name", "Vacation", "Education", "Color", "PhoneModel", "Food"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()