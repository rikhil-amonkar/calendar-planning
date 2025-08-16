from z3 import *
import json

def main():
    solver = Solver()
    houses = 6

    # Each house has a name, a height, and a phone.
    # We represent each attribute as an Int variable with possible values 0 to 5.
    names = [Int(f"name_{i}") for i in range(houses)]
    heights = [Int(f"height_{i}") for i in range(houses)]
    phones = [Int(f"phone_{i}") for i in range(houses)]

    # Constrain each variable to be in the proper range.
    for i in range(houses):
        solver.add(names[i] >= 0, names[i] <= 5)
        solver.add(heights[i] >= 0, heights[i] <= 5)
        solver.add(phones[i] >= 0, phones[i] <= 5)

    # All different for each attribute.
    solver.add(Distinct(names))
    solver.add(Distinct(heights))
    solver.add(Distinct(phones))

    # Define our enumerations.
    # Names: 0:"Alice", 1:"Eric", 2:"Bob", 3:"Peter", 4:"Arnold", 5:"Carol"
    ALICE, ERIC, BOB, PETER, ARNOLD, CAROL = 0, 1, 2, 3, 4, 5

    # Heights: 0:"very tall", 1:"tall", 2:"super tall", 3:"average", 4:"very short", 5:"short"
    VERY_TALL, TALL, SUPER_TALL, AVERAGE, VERY_SHORT, SHORT = 0, 1, 2, 3, 4, 5

    # Phones: 0:"oneplus 9", 1:"google pixel 6", 2:"samsung galaxy s21", 3:"iphone 13", 4:"huawei p50", 5:"xiaomi mi 11"
    ONEPLUS_9, GOOGLE_PIXEL, SAMSUNG, IPHONE, HUAWEI, XIAOMI = 0, 1, 2, 3, 4, 5

    # -------------------- Add the puzzle constraints --------------------

    # Clue 9: "The person who is super tall is in the first house."
    solver.add(heights[0] == SUPER_TALL)

    # Clue 12: "The person who is short is in the sixth house."
    solver.add(heights[5] == SHORT)

    # Clue 5: "There is one house between the person who uses a Google Pixel 6 and the person who is short."
    # Since the person who is short is in house 6 (index 5), the only possibility is that the Google Pixel 6 user is in house 4 (index 3).
    solver.add(phones[3] == GOOGLE_PIXEL)

    # Clue 7: "The person who uses a OnePlus 9 is directly left of the person who is short."
    # With house 6 (index 5) being short, the OnePlus 9 must be in house 5 (index 4).
    solver.add(phones[4] == ONEPLUS_9)

    # Clue 6: "The person who uses a Samsung Galaxy S21 is not in the first house."
    solver.add(phones[0] != SAMSUNG)

    # Clue 10: "The person who uses a Xiaomi Mi 11 is Carol."
    # Carol’s phone must be Xiaomi Mi 11 and vice‐versa.
    for i in range(houses):
        solver.add(Implies(names[i] == CAROL, phones[i] == XIAOMI))
        solver.add(Implies(phones[i] == XIAOMI, names[i] == CAROL))

    # Clue 8: "The person who is tall is Arnold."
    # So if a house is occupied by Arnold then its height must be tall; and if a house has height tall then its occupant is Arnold.
    for i in range(houses):
        solver.add(Implies(names[i] == ARNOLD, heights[i] == TALL))
        solver.add(Implies(heights[i] == TALL, names[i] == ARNOLD))
    
    # Clue 1: "Bob is directly left of the person who is tall."
    # Because from Clue 8 the tall person is Arnold, whenever a house (except the first) has Arnold,
    # the house immediately to its left must have Bob.
    for i in range(1, houses):
        solver.add(Implies(names[i] == ARNOLD, names[i-1] == BOB))
    # Also, Arnold cannot be in the first house.
    solver.add(names[0] != ARNOLD)

    # Clue 4: "Carol is the person who is very tall."
    # So Carol’s height is very tall and likewise if a house has height very tall then its occupant is Carol.
    for i in range(houses):
        solver.add(Implies(names[i] == CAROL, heights[i] == VERY_TALL))
        solver.add(Implies(heights[i] == VERY_TALL, names[i] == CAROL))

    # Clue 2: "Peter is somewhere to the left of the person who uses an iPhone 13."
    # iPhone 13 is represented as IPHONE.
    for j in range(houses):
        if j > 0:
            solver.add(Implies(phones[j] == IPHONE, Or([names[i] == PETER for i in range(j)])))
        else:
            # In the first house no one is to its left so it cannot be the iPhone 13 user.
            solver.add(phones[j] != IPHONE)

    # Clue 11: "The person who uses a Google Pixel 6 is somewhere to the right of Eric."
    # Since the Google Pixel 6 is forced to house 4 (index 3), Eric must be in one of houses 1, 2, or 3 (indices 0, 1, 2).
    for i in range(3, houses):
        solver.add(names[i] != ERIC)

    # Clue 3: "The person who is very short is somewhere to the right of the person who uses a Google Pixel 6."
    # With the Google Pixel 6 in house 4 (index 3) and the short person in house 6 (index 5),
    # the only available slot for the very short person is house 5 (index 4).
    solver.add(heights[4] == VERY_SHORT)

    # --------------------------------------------------------------------

    # Solve the puzzle.
    if solver.check() == sat:
        model = solver.model()

        # Define mappings from our integer codes to the corresponding strings.
        name_map = {ALICE: "Alice", ERIC: "Eric", BOB: "Bob", PETER: "Peter", ARNOLD: "Arnold", CAROL: "Carol"}
        height_map = {
            VERY_TALL: "very tall",
            TALL: "tall",
            SUPER_TALL: "super tall",
            AVERAGE: "average",
            VERY_SHORT: "very short",
            SHORT: "short"
        }
        phone_map = {
            ONEPLUS_9: "oneplus 9",
            GOOGLE_PIXEL: "google pixel 6",
            SAMSUNG: "samsung galaxy s21",
            IPHONE: "iphone 13",
            HUAWEI: "huawei p50",
            XIAOMI: "xiaomi mi 11"
        }
        
        # Build a list of rows in house order (houses are numbered 1..6).
        rows = []
        for i in range(houses):
            house_num = str(i + 1)
            n_val = model.evaluate(names[i]).as_long()
            h_val = model.evaluate(heights[i]).as_long()
            p_val = model.evaluate(phones[i]).as_long()
            rows.append([house_num, name_map[n_val], height_map[h_val], phone_map[p_val]])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Height", "PhoneModel"],
                "rows": rows
            }
        }
        
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()