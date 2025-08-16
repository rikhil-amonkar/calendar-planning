from z3 import Solver, String, Int, Distinct, If, Or, And, sat
import json

def main():
    names = ["Arnold", "Peter", "Eric", "Alice"]
    house_styles = ["craftsman", "colonial", "victorian", "ranch"]
    hair_colors = ["red", "blonde", "black", "brown"]
    children = ["Bella", "Fred", "Meredith", "Samantha"]
    book_genres = ["mystery", "fantasy", "romance", "science fiction"]
    
    n = [String(f'n_{i}') for i in range(4)]
    hs = [String(f'hs_{i}') for i in range(4)]
    hc = [String(f'hc_{i}') for i in range(4)]
    ch = [String(f'ch_{i}') for i in range(4)]
    bg = [String(f'bg_{i}') for i in range(4)]
    
    s = Solver()
    
    s.add(Distinct(n))
    s.add(Distinct(hs))
    s.add(Distinct(hc))
    s.add(Distinct(ch))
    s.add(Distinct(bg))
    
    for i in range(4):
        s.add(Or([n[i] == nm for nm in names]))
        s.add(Or([hs[i] == style for style in house_styles]))
        s.add(Or([hc[i] == color for color in hair_colors]))
        s.add(Or([ch[i] == child for child in children]))
        s.add(Or([bg[i] == genre for genre in book_genres]))
    
    s.add(hs[2] == "craftsman")
    
    for i in range(4):
        s.add(If(n[i] == "Alice", bg[i] == "romance", True))
    
    s.add(hc[3] == "brown")
    s.add(ch[3] == "Samantha")
    
    red_index = Int('red_index')
    ranch_index = Int('ranch_index')
    s.add(red_index >= 0, red_index < 4)
    s.add(ranch_index >= 0, ranch_index < 4)
    for i in range(4):
        s.add(If(hc[i] == "red", red_index == i, True))
        s.add(If(hs[i] == "ranch", ranch_index == i, True))
    s.add(ranch_index > red_index)
    
    for i in range(4):
        s.add(If(n[i] == "Peter", ch[i] == "Bella", True))
    
    for i in range(4):
        s.add(If(n[i] == "Arnold", hc[i] == "red", True))
    
    for i in range(4):
        s.add(If(n[i] == "Alice", hs[i] == "colonial", True))
    
    s.add(hc[1] == "black")
    
    for i in range(4):
        s.add(If(n[i] == "Peter", bg[i] == "fantasy", True))
    
    for i in range(4):
        s.add(If(n[i] == "Arnold", ch[i] == "Meredith", True))
    
    for i in range(4):
        s.add(If(hc[i] == "black", n[i] == "Eric", True))
    
    for i in range(4):
        s.add(If(n[i] == "Arnold", bg[i] == "science fiction", True))
    
    if s.check() == sat:
        m = s.model()
        rows = []
        for i in range(4):
            name_val = m.eval(n[i]).as_string()
            style_val = m.eval(hs[i]).as_string()
            color_val = m.eval(hc[i]).as_string()
            child_val = m.eval(ch[i]).as_string()
            genre_val = m.eval(bg[i]).as_string()
            rows.append([str(i+1), name_val, style_val, color_val, child_val, genre_val])
        
        result = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "HairColor", "Children", "BookGenre"],
                "rows": rows
            }
        }
        print(json.dumps(result))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()