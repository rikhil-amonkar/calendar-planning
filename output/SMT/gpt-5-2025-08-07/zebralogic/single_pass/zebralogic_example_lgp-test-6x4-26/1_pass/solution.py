import json
from z3 import Solver, Ints, Int, Distinct, Or, And

def solve():
    # Domains
    houses = list(range(6))  # 0..5 represent houses 1..6
    
    Names = ["Peter", "Bob", "Carol", "Eric", "Alice", "Arnold"]
    Pets = ["bird", "dog", "cat", "rabbit", "fish", "hamster"]
    Styles = ["victorian", "ranch", "modern", "mediterranean", "colonial", "craftsman"]
    Birthdays = ["mar", "sept", "may", "feb", "jan", "april"]
    
    # Index maps
    idx_name = {n:i for i,n in enumerate(Names)}
    idx_pet = {p:i for i,p in enumerate(Pets)}
    idx_style = {s:i for i,s in enumerate(Styles)}
    idx_bday = {b:i for i,b in enumerate(Birthdays)}
    
    # Position variables: position of each value (0..5)
    pos_name = [Int(f"pos_name_{n}") for n in Names]
    pos_pet = [Int(f"pos_pet_{p}") for p in Pets]
    pos_style = [Int(f"pos_style_{s}") for s in Styles]
    pos_bday = [Int(f"pos_bday_{b}") for b in Birthdays]
    
    s = Solver()
    
    # Domains
    for arr in [pos_name, pos_pet, pos_style, pos_bday]:
        for v in arr:
            s.add(And(v >= 0, v <= 5))
        s.add(Distinct(*arr))
    
    # Helper to get pos by label
    def PN(n): return pos_name[idx_name[n]]
    def PP(p): return pos_pet[idx_pet[p]]
    def PS(st): return pos_style[idx_style[st]]
    def PB(b): return pos_bday[idx_bday[b]]
    
    # Clues encoding
    
    # 1. hamster right of March
    s.add(PP("hamster") > PB("mar"))
    # 2. January left of September
    s.add(PB("jan") < PB("sept"))
    # 3. May in the second house (index 1)
    s.add(PB("may") == 1)
    # 4. Colonial in the second house
    s.add(PS("colonial") == 1)
    # 5. Carol is in the third house
    s.add(PN("Carol") == 2)
    # 6. Mediterranean not in the sixth house
    s.add(PS("mediterranean") != 5)
    # 7. Fish is somewhere to the right of Bob
    s.add(PP("fish") > PN("Bob"))
    # 8. Eric is in the sixth house
    s.add(PN("Eric") == 5)
    # 9. One house between cat and Victorian
    s.add(Or(PP("cat") == PS("victorian") + 2, PS("victorian") == PP("cat") + 2))
    # 10. Two houses between Victorian and hamster
    s.add(Or(PS("victorian") == PP("hamster") + 3, PP("hamster") == PS("victorian") + 3))
    # 11. Craftsman is Arnold
    s.add(PS("craftsman") == PN("Arnold"))
    # 12. Colonial left of modern
    s.add(PS("colonial") < PS("modern"))
    # 13. Fish not in the second house
    s.add(PP("fish") != 1)
    # 14. Peter is the person living in a colonial-style house
    s.add(PN("Peter") == PS("colonial"))
    # 15. January directly left of April
    s.add(PB("april") == PB("jan") + 1)
    # 16. One house between bird and modern
    s.add(Or(PP("bird") == PS("modern") + 2, PS("modern") == PP("bird") + 2))
    # 17. Carol is March
    s.add(PB("mar") == PN("Carol"))
    # 18. Craftsman in the fourth house
    s.add(PS("craftsman") == 3)
    # 19. Dog in the fourth house
    s.add(PP("dog") == 3)
    
    if s.check() != sat:
        raise RuntimeError("No solution found")
    m = s.model()
    
    # Build reverse maps: house -> value
    house_to_name = [""] * 6
    house_to_pet = [""] * 6
    house_to_style = [""] * 6
    house_to_bday = [""] * 6
    
    for n in Names:
        house_to_name[m.evaluate(PN(n)).as_long()] = n
    for p in Pets:
        house_to_pet[m.evaluate(PP(p)).as_long()] = p
    for st in Styles:
        house_to_style[m.evaluate(PS(st)).as_long()] = st
    for b in Birthdays:
        house_to_bday[m.evaluate(PB(b)).as_long()] = b
    
    # Prepare JSON
    rows = []
    for i in range(6):
        rows.append([
            str(i+1),
            house_to_name[i],
            house_to_pet[i],
            house_to_style[i],
            house_to_bday[i],
        ])
    
    output = {
        "solution": {
            "header": ["House", "Name", "Pet", "HouseStyle", "Birthday"],
            "rows": rows
        }
    }
    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve()