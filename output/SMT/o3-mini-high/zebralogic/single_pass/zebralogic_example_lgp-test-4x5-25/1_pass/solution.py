from z3 import *
import json

def solve_puzzle():
    solver = Solver()
    n = 4  # four houses, indexed 0 to 3 corresponding to House 1..4

    # Create Z3 integer variables for each attribute in each house.
    # We will use numbers 0 to 3 to represent the four possibilities in each category.
    names      = [Int(f"name_{i}") for i in range(n)]
    houseStyles = [Int(f"houseStyle_{i}") for i in range(n)]
    hairs      = [Int(f"hair_{i}") for i in range(n)]
    children   = [Int(f"child_{i}") for i in range(n)]
    books      = [Int(f"book_{i}") for i in range(n)]

    # Domain constraints: each variable is in {0,1,2,3}.
    for group in [names, houseStyles, hairs, children, books]:
        for var in group:
            solver.add(And(var >= 0, var < n))

    # Each attribute appears exactly once.
    solver.add(Distinct(names))
    solver.add(Distinct(houseStyles))
    solver.add(Distinct(hairs))
    solver.add(Distinct(children))
    solver.add(Distinct(books))

    # We use the following mappings:
    # Names:         Arnold=0,   Peter=1,   Eric=2,   Alice=3
    # HouseStyle:    craftsman=0, colonial=1, victorian=2, ranch=3
    # Hair:          red=0,      blonde=1,   black=2,  brown=3
    # Children:      Bella=0,    Fred=1,     Meredith=2, Samantha=3
    # BookGenre:     mystery=0,  fantasy=1,  romance=2, science fiction=3

    # Clue 1: The person in a Craftsman-style house is in the third house.
    solver.add(houseStyles[2] == 0)  # House 3 gets craftsman.

    # Clue 3: The person who has brown hair is in the fourth house.
    solver.add(hairs[3] == 3)  # House 4 gets brown hair.

    # Clue 4: The person's child is named Samantha is in the fourth house.
    solver.add(children[3] == 3)  # House 4's child is Samantha.

    # Clue 9: The person who has black hair is in the second house.
    solver.add(hairs[1] == 2)  # House 2 gets black hair.

    # For every house, add conditional constraints:
    for i in range(n):
        # Clue 2: Alice loves romance books.
        solver.add(Implies(names[i] == 3, books[i] == 2))
        # Clue 8: Alice lives in a colonial-style house.
        solver.add(Implies(names[i] == 3, houseStyles[i] == 1))
        # Clue 6: Peter’s child is named Bella.
        solver.add(Implies(names[i] == 1, children[i] == 0))
        # Clue 10: The person who loves fantasy books is Peter.
        solver.add(Implies(names[i] == 1, books[i] == 1))
        # Clue 7: Arnold has red hair.
        solver.add(Implies(names[i] == 0, hairs[i] == 0))
        # Clue 11: Arnold’s child is named Meredith.
        solver.add(Implies(names[i] == 0, children[i] == 2))
        # Clue 13: The person who loves science fiction books is Arnold.
        solver.add(Implies(names[i] == 0, books[i] == 3))
        # Clue 12: The person who has black hair is Eric.
        solver.add(Implies(hairs[i] == 2, names[i] == 2))

    # Clue 5: The person in a ranch-style home is somewhere to the right of the person who has red hair.
    # Because exactly one person has red hair and exactly one house is ranch,
    # we enforce that for all houses i and j, if house i has red hair and house j is ranch then i < j.
    for i in range(n):
        for j in range(n):
            solver.add(Implies(And(hairs[i] == 0, houseStyles[j] == 3), i < j))
    
    # Solve the constraints.
    if solver.check() == sat:
        m = solver.model()
        # Mappings from numbers back to strings.
        name_map = {0: "Arnold", 1: "Peter", 2: "Eric", 3: "Alice"}
        style_map = {0: "craftsman", 1: "colonial", 2: "victorian", 3: "ranch"}
        hair_map = {0: "red", 1: "blonde", 2: "black", 3: "brown"}
        child_map = {0: "Bella", 1: "Fred", 2: "Meredith", 3: "Samantha"}
        book_map = {0: "mystery", 1: "fantasy", 2: "romance", 3: "science fiction"}
        
        rows = []
        for i in range(n):
            house_number = str(i + 1)
            name_str = name_map[m[names[i]].as_long()]
            style_str = style_map[m[houseStyles[i]].as_long()]
            hair_str = hair_map[m[hairs[i]].as_long()]
            child_str = child_map[m[children[i]].as_long()]
            book_str = book_map[m[books[i]].as_long()]
            rows.append([house_number, name_str, style_str, hair_str, child_str, book_str])
        
        result = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "HairColor", "Children", "BookGenre"],
                "rows": rows
            }
        }
        print(json.dumps(result, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    solve_puzzle()