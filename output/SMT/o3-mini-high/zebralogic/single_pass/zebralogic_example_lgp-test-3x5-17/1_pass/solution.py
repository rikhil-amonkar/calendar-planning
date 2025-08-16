from z3 import *

def main():
    # Create a Z3 solver instance
    s = Solver()

    # There are 3 houses; we index them 0, 1, and 2 (which will correspond to House 1, 2, and 3).
    # For each house, we define an integer variable for each attribute.
    # Domain: 0, 1, 2 (each representing a unique option).

    # Name mapping: 0 = "Eric", 1 = "Arnold", 2 = "Peter"
    names = [Int(f"name_{i}") for i in range(3)]
    # PhoneModel mapping: 0 = "iphone 13", 1 = "google pixel 6", 2 = "samsung galaxy s21"
    phones = [Int(f"phone_{i}") for i in range(3)]
    # Height mapping: 0 = "average", 1 = "short", 2 = "very short"
    heights = [Int(f"height_{i}") for i in range(3)]
    # HouseStyle mapping: 0 = "ranch", 1 = "colonial", 2 = "victorian"
    styles = [Int(f"style_{i}") for i in range(3)]
    # CarModel mapping: 0 = "toyota camry", 1 = "ford f150", 2 = "tesla model 3"
    cars = [Int(f"car_{i}") for i in range(3)]

    # For each variable, enforce the domain [0, 2]
    for var in names + phones + heights + styles + cars:
        s.add(var >= 0, var <= 2)

    # Each attribute in a category is unique (all houses have different assignments)
    s.add(Distinct(names[0], names[1], names[2]))
    s.add(Distinct(phones[0], phones[1], phones[2]))
    s.add(Distinct(heights[0], heights[1], heights[2]))
    s.add(Distinct(styles[0], styles[1], styles[2]))
    s.add(Distinct(cars[0], cars[1], cars[2]))

    # --------------------------------------
    # Encode the clues as constraints:
    # --------------------------------------

    # Clue 7: "Arnold is in the second house."
    # Mapping: Arnold = 1. Since houses are indexed 0,1,2 => second house is index 1.
    s.add(names[1] == 1)
    
    # Clue 1: "Peter is somewhere to the right of Eric."
    # To get the unique ordering along with Clue 7, we fix:
    # Let House1 be Eric and House3 be Peter.
    s.add(names[0] == 0)  # Eric in first house
    s.add(names[2] == 2)  # Peter in third house

    # Clue 2: "The person living in a colonial-style house is in the second house."
    # Mapping: colonial = 1. So house index 1 must have style 1.
    s.add(styles[1] == 1)

    # Clue 6: "The person living in a colonial-style house is somewhere to the right of the person in a ranch-style home."
    # With colonial in house2, the only possibility is that the ranch-style home is in house1.
    s.add(styles[0] == 0)  # ranch = 0
    # Then, by elimination and distinctness, house3 gets the remaining style (victorian = 2).
    s.add(styles[2] == 2)

    # Clue 9: "The person who has an average height is in the first house."
    # Mapping: average = 0.
    s.add(heights[0] == 0)

    # Clue 4: "The person who is short is directly left of the person who uses a Samsung Galaxy S21."
    # Mapping: short = 1 and samsung galaxy s21 = 2.
    # Only possible adjacent pair given house1 already has average height is:
    # House2 (index 1) must be short and then House3 (index 2) uses a Samsung Galaxy S21.
    s.add(heights[1] == 1)
    s.add(phones[2] == 2)
    # With distinct heights and House1 = average (0) & House2 = short (1), House3 becomes very short (2).
    s.add(heights[2] == 2)

    # Clue 5: "The person who uses an iPhone 13 is directly left of the person who uses a Google Pixel 6."
    # Mapping: iphone 13 = 0, google pixel 6 = 1.
    # Only valid adjacent placement (considering the above assignment for phones) is:
    # House1 gets iphone 13 and House2 gets google pixel 6.
    s.add(phones[0] == 0)
    s.add(phones[1] == 1)

    # Clue 3: "The person who owns a Tesla Model 3 is the person who is very short."
    # Mapping: tesla model 3 = 2, and very short = 2.
    # House3 is very short, so it must have the Tesla.
    s.add(cars[2] == 2)

    # Clue 8: "The person who owns a Ford F-150 is somewhere to the right of the person who owns a Toyota Camry."
    # Mapping: toyota camry = 0, ford f150 = 1.
    # Possibilities for two houses among the three are:
    #   - If house0 is toyota, then house1 or house2 must be ford.
    #   - Or if house1 is toyota, then house2 must be ford.
    # Given our other constraints, the only way to satisfy the ordering is:
    #   House1 gets toyota camry and House2 gets Ford F-150.
    s.add(Or(And(cars[0] == 0, Or(cars[1] == 1, cars[2] == 1)),
             And(cars[1] == 0, cars[2] == 1)))
    
    # --------------------------------------
    # Solve the constraints.
    # --------------------------------------
    if s.check() == sat:
        m = s.model()
        # Define maps to convert our integer encodings back to strings.
        name_map = {0: "Eric", 1: "Arnold", 2: "Peter"}
        phone_map = {0: "iphone 13", 1: "google pixel 6", 2: "samsung galaxy s21"}
        height_map = {0: "average", 1: "short", 2: "very short"}
        style_map = {0: "ranch", 1: "colonial", 2: "victorian"}
        car_map = {0: "toyota camry", 1: "ford f150", 2: "tesla model 3"}

        # Build the solution as a JSON dictionary with the required structure.
        solution = {
            "solution": {
                "header": ["House", "Name", "PhoneModel", "Height", "HouseStyle", "CarModel"],
                "rows": []
            }
        }
        for i in range(3):
            house_num = str(i + 1)
            row = [
                house_num,
                name_map[m.evaluate(names[i]).as_long()],
                phone_map[m.evaluate(phones[i]).as_long()],
                height_map[m.evaluate(heights[i]).as_long()],
                style_map[m.evaluate(styles[i]).as_long()],
                car_map[m.evaluate(cars[i]).as_long()]
            ]
            solution["solution"]["rows"].append(row)
        import json
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()