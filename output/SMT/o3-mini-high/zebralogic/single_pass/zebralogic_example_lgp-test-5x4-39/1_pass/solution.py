from z3 import Solver, Int, And, Distinct, Abs
import json

def main():
    s = Solver()

    # Define variables for the house positions (1-5) for each attribute.
    # Names: Arnold, Peter, Eric, Alice, Bob.
    names = {
        "Arnold": Int("Arnold"),
        "Peter": Int("Peter"),
        "Eric": Int("Eric"),
        "Alice": Int("Alice"),
        "Bob": Int("Bob")
    }
    
    # Hobbies: painting, cooking, knitting, gardening, photography.
    hobbies = {
        "painting": Int("painting"),
        "cooking": Int("cooking"),
        "knitting": Int("knitting"),
        "gardening": Int("gardening"),
        "photography": Int("photography")
    }
    
    # Heights: very tall, tall, very short, average, short.
    heights = {
        "very tall": Int("very_tall"),
        "tall": Int("tall"),
        "very short": Int("very_short"),
        "average": Int("average"),
        "short": Int("short")
    }
    
    # Foods: stew, grilled cheese, stir fry, spaghetti, pizza.
    foods = {
        "stew": Int("stew"),
        "grilled cheese": Int("grilled_cheese"),
        "stir fry": Int("stir_fry"),
        "spaghetti": Int("spaghetti"),
        "pizza": Int("pizza")
    }
    
    # All variables must be in house positions 1 to 5.
    all_vars = list(names.values()) + list(hobbies.values()) + list(heights.values()) + list(foods.values())
    for var in all_vars:
        s.add(And(var >= 1, var <= 5))
        
    # Ensure all attributes within each category are in distinct houses.
    s.add(Distinct(list(names.values())))
    s.add(Distinct(list(hobbies.values())))
    s.add(Distinct(list(heights.values())))
    s.add(Distinct(list(foods.values())))
    
    # Now add the clues as constraints.
    #
    # Clue 1: Bob is the photography enthusiast.
    s.add(names["Bob"] == hobbies["photography"])
    
    # Clue 2: The person who loves eating grilled cheese is the person who is tall.
    s.add(foods["grilled cheese"] == heights["tall"])
    
    # Clue 3: Peter is not in the second house.
    s.add(names["Peter"] != 2)
    
    # Clue 4: The person who is tall is directly left of the person who loves stir fry.
    s.add(heights["tall"] + 1 == foods["stir fry"])
    
    # Clue 5: The person who loves cooking is the person who has an average height.
    s.add(hobbies["cooking"] == heights["average"])
    
    # Clue 6: Alice is directly left of the person who is a pizza lover.
    s.add(names["Alice"] + 1 == foods["pizza"])
    
    # Clue 7: The person who loves spaghetti is not in the second house.
    s.add(foods["spaghetti"] != 2)
    
    # Clue 8: Eric is not in the fifth house.
    s.add(names["Eric"] != 5)
    
    # Clue 9: The person who is short is Peter.
    s.add(heights["short"] == names["Peter"])
    
    # Clue 10: The person who has an average height and the person who enjoys gardening are next to each other.
    s.add(Abs(heights["average"] - hobbies["gardening"]) == 1)
    
    # Clue 11: The person who paints as a hobby is directly left of the person who loves eating grilled cheese.
    s.add(hobbies["painting"] + 1 == foods["grilled cheese"])
    
    # Clue 12: The person who is very short is in the fifth house.
    s.add(heights["very short"] == 5)
    
    # Clue 13: The person who is tall is in the third house.
    s.add(heights["tall"] == 3)
    
    # Clue 14: Alice is somewhere to the right of the photography enthusiast.
    # Since Bob is the photography enthusiast (clue 1), we require:
    s.add(names["Alice"] > names["Bob"])
    
    # Check for a solution.
    if s.check() == 0:  # unsat
        print("No solution found")
        return
        
    m = s.model()
    
    # Helper: invert a dictionary (attribute -> house number) to (house number -> attribute)
    def invert_dict(d):
        inv = {}
        for key, var in d.items():
            inv[m.evaluate(var).as_long()] = key
        return inv
    
    names_inv = invert_dict(names)
    hobbies_inv = invert_dict(hobbies)
    heights_inv = invert_dict(heights)
    foods_inv = invert_dict(foods)
    
    # Build the rows sorted by house number.
    rows = []
    for house in range(1, 6):
        row = [
            str(house),
            names_inv[house],
            hobbies_inv[house],
            heights_inv[house],
            foods_inv[house]
        ]
        rows.append(row)
    
    output = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Height", "Food"],
            "rows": rows
        }
    }
    
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()