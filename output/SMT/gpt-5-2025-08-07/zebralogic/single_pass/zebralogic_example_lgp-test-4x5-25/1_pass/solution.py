import json
from z3 import *

def solve_puzzle():
    # Enumerations
    names = ["Arnold", "Peter", "Eric", "Alice"]
    styles = ["craftsman", "colonial", "victorian", "ranch"]
    hairs = ["red", "blonde", "black", "brown"]
    children = ["Bella", "Fred", "Meredith", "Samantha"]
    books = ["mystery", "fantasy", "romance", "science fiction"]

    n_houses = 4

    # Helper to get index
    def idx(lst, val): 
        return lst.index(val)

    # Variables: position (house index 0..3) of each attribute value
    name_pos = [Int(f"name_pos_{n}") for n in names]
    style_pos = [Int(f"style_pos_{s}") for s in styles]
    hair_pos = [Int(f"hair_pos_{h}") for h in hairs]
    child_pos = [Int(f"child_pos_{c}") for c in children]
    book_pos = [Int(f"book_pos_{b}") for b in books]

    s = Solver()

    # Domains: all positions are within 0..3
    for arr in (name_pos, style_pos, hair_pos, child_pos, book_pos):
        for v in arr:
            s.add(v >= 0, v < n_houses)

    # All different within each attribute set (bijective mapping to houses)
    s.add(Distinct(name_pos))
    s.add(Distinct(style_pos))
    s.add(Distinct(hair_pos))
    s.add(Distinct(child_pos))
    s.add(Distinct(book_pos))

    # Clues as constraints:

    # 1. The person in a Craftsman-style house is in the third house.
    s.add(style_pos[idx(styles, "craftsman")] == 2)

    # 2. Alice is the person who loves romance books.
    s.add(name_pos[idx(names, "Alice")] == book_pos[idx(books, "romance")])

    # 3. The person who has brown hair is in the fourth house.
    s.add(hair_pos[idx(hairs, "brown")] == 3)

    # 4. The person's child is named Samantha is in the fourth house.
    s.add(child_pos[idx(children, "Samantha")] == 3)

    # 5. The person in a ranch-style home is somewhere to the right of the person who has red hair.
    s.add(style_pos[idx(styles, "ranch")] > hair_pos[idx(hairs, "red")])

    # 6. Peter is the person's child is named Bella. (Peter's child is Bella)
    s.add(name_pos[idx(names, "Peter")] == child_pos[idx(children, "Bella")])

    # 7. Arnold is the person who has red hair.
    s.add(name_pos[idx(names, "Arnold")] == hair_pos[idx(hairs, "red")])

    # 8. Alice is the person living in a colonial-style house.
    s.add(name_pos[idx(names, "Alice")] == style_pos[idx(styles, "colonial")])

    # 9. The person who has black hair is in the second house.
    s.add(hair_pos[idx(hairs, "black")] == 1)

    # 10. The person who loves fantasy books is Peter.
    s.add(name_pos[idx(names, "Peter")] == book_pos[idx(books, "fantasy")])

    # 11. Arnold is the person's child is named Meredith. (Arnold's child is Meredith)
    s.add(name_pos[idx(names, "Arnold")] == child_pos[idx(children, "Meredith")])

    # 12. The person who has black hair is Eric.
    s.add(name_pos[idx(names, "Eric")] == hair_pos[idx(hairs, "black")])

    # 13. The person who loves science fiction books is Arnold.
    s.add(name_pos[idx(names, "Arnold")] == book_pos[idx(books, "science fiction")])

    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()

    # Invert positions to get house -> attribute value
    house_to_name = [""] * n_houses
    house_to_style = [""] * n_houses
    house_to_hair = [""] * n_houses
    house_to_child = [""] * n_houses
    house_to_book = [""] * n_houses

    for i, n in enumerate(names):
        house_to_name[m[name_pos[i]].as_long()] = n
    for i, st in enumerate(styles):
        house_to_style[m[style_pos[i]].as_long()] = st
    for i, h in enumerate(hairs):
        house_to_hair[m[hair_pos[i]].as_long()] = h
    for i, c in enumerate(children):
        house_to_child[m[child_pos[i]].as_long()] = c
    for i, b in enumerate(books):
        house_to_book[m[book_pos[i]].as_long()] = b

    # Build the required JSON structure
    result = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "HairColor", "Children", "BookGenre"],
            "rows": []
        }
    }

    for house_idx in range(n_houses):
        row = [
            str(house_idx + 1),
            house_to_name[house_idx],
            house_to_style[house_idx],
            house_to_hair[house_idx],
            house_to_child[house_idx],
            house_to_book[house_idx],
        ]
        result["solution"]["rows"].append(row)

    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution))