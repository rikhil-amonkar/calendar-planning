from z3 import *

def main():
    s = Solver()
    houses = 3

    # Create Z3 integer variables for each house and each attribute.
    names     = [Int(f"name_{i}") for i in range(houses)]
    books     = [Int(f"book_{i}") for i in range(houses)]
    smoothies = [Int(f"smoothie_{i}") for i in range(houses)]
    birthdays = [Int(f"birthday_{i}") for i in range(houses)]
    heights   = [Int(f"height_{i}") for i in range(houses)]
    
    # Each attribute can take one of three distinct values: 0, 1, or 2.
    for i in range(houses):
        s.add(And(names[i]     >= 0, names[i]     <= 2))
        s.add(And(books[i]     >= 0, books[i]     <= 2))
        s.add(And(smoothies[i] >= 0, smoothies[i] <= 2))
        s.add(And(birthdays[i] >= 0, birthdays[i] <= 2))
        s.add(And(heights[i]   >= 0, heights[i]   <= 2))
    
    # All attributes must be assigned distinct values across houses.
    s.add(Distinct(names[0], names[1], names[2]))
    s.add(Distinct(books[0], books[1], books[2]))
    s.add(Distinct(smoothies[0], smoothies[1], smoothies[2]))
    s.add(Distinct(birthdays[0], birthdays[1], birthdays[2]))
    s.add(Distinct(heights[0], heights[1], heights[2]))
    
    # Define our mapping:
    # Names: Peter=0, Arnold=1, Eric=2
    # Book genres: science fiction=0, mystery=1, romance=2
    # Smoothies: watermelon=0, desert=1, cherry=2
    # Birthdays: april=0, jan=1, sept=2
    # Heights: average=0, very short=1, short=2

    # Clue 7: Eric is in the first house (house index 0).
    s.add(names[0] == 2)
    # Clue 9: The Watermelon smoothie lover is Eric.
    s.add(smoothies[0] == 0)
    s.add(Implies(names[0] == 2, smoothies[0] == 0))
    s.add(Implies(smoothies[0] == 0, names[0] == 2))
    # Clue 8: The Watermelon smoothie lover is the person who is short.
    s.add(Implies(smoothies[0] == 0, heights[0] == 2))
    s.add(Implies(heights[0] == 2, smoothies[0] == 0))
    
    # Clue 3: The person whose birthday is in January (1) is not in the first house.
    s.add(birthdays[0] != 1)
    
    # Clue 1: The person who likes Cherry smoothies (2) is not in the second house (index 1).
    s.add(smoothies[1] != 2)
    
    # For every house, add the rest of the constraints using implications:
    for i in range(houses):
        # Clue 4: The person who is very short (height == 1) is the person who loves romance books (book == 2).
        s.add(Implies(books[i] == 2, heights[i] == 1))
        s.add(Implies(heights[i] == 1, books[i] == 2))
        # Clue 2: Arnold is the person who loves mystery books.
        s.add(Implies(names[i] == 1, books[i] == 1))
        # Clue 5: The person who loves mystery books (1) is the person whose birthday is in September (2).
        s.add(Implies(books[i] == 1, birthdays[i] == 2))
        s.add(Implies(birthdays[i] == 2, books[i] == 1))
        # Clue 6: The person who has an average height (0) is the Desert smoothie lover (1).
        s.add(Implies(heights[i] == 0, smoothies[i] == 1))
        s.add(Implies(smoothies[i] == 1, heights[i] == 0))
        # Also, enforce the watermelon-short connection for any house.
        s.add(Implies(smoothies[i] == 0, heights[i] == 2))
        s.add(Implies(heights[i] == 2, smoothies[i] == 0))
        # And the Eric-watermelon two-way condition.
        s.add(Implies(names[i] == 2, smoothies[i] == 0))
        s.add(Implies(smoothies[i] == 0, names[i] == 2))
    
    # Solve the constraints.
    if s.check() == sat:
        mdl = s.model()
        # Mapping dictionaries to convert integer values to strings.
        name_map     = {0: "Peter", 1: "Arnold", 2: "Eric"}
        book_map     = {0: "science fiction", 1: "mystery", 2: "romance"}
        smoothie_map = {0: "watermelon", 1: "desert", 2: "cherry"}
        birthday_map = {0: "april", 1: "jan", 2: "sept"}
        height_map   = {0: "average", 1: "very short", 2: "short"}

        rows = []
        for i in range(houses):
            house_number = str(i + 1)  # House numbers: 1, 2, 3
            row = [
                house_number,
                name_map[mdl[names[i]].as_long()],
                book_map[mdl[books[i]].as_long()],
                smoothie_map[mdl[smoothies[i]].as_long()],
                birthday_map[mdl[birthdays[i]].as_long()],
                height_map[mdl[heights[i]].as_long()]
            ]
            rows.append(row)
    
        solution = {
            "solution": {
                "header": ["House", "Name", "BookGenre", "Smoothie", "Birthday", "Height"],
                "rows": rows
            }
        }
        import json
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()