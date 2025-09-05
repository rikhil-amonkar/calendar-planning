import json
from z3 import Solver, Int, Or, Distinct, sat

def main():
    s = Solver()
    
    num_houses = 2
    
    # Mapping:
    # Names: 0 -> "Eric", 1 -> "Arnold"
    # BookGenres: 0 -> "science fiction", 1 -> "mystery"
    name_vars = [Int(f"name_{i}") for i in range(1, num_houses+1)]
    genre_vars = [Int(f"genre_{i}") for i in range(1, num_houses+1)]
    
    # Domain constraints for names and book genres
    for nv in name_vars:
        s.add(Or(nv == 0, nv == 1))
    for gv in genre_vars:
        s.add(Or(gv == 0, gv == 1))
    
    # They must be all distinct
    s.add(Distinct(name_vars))
    s.add(Distinct(genre_vars))
    
    # Clue 1: Eric is directly left of the person who loves mystery books.
    # With two houses (house 1 is left of house 2), this implies:
    # House 1 is Eric (0) and House 2 loves mystery (1).
    s.add(name_vars[0] == 0)   # House 1: Eric
    s.add(genre_vars[1] == 1)  # House 2: mystery
    
    if s.check() == sat:
        model = s.model()
        name_map = {0: "Eric", 1: "Arnold"}
        genre_map = {0: "science fiction", 1: "mystery"}
        
        rows = []
        for i in range(num_houses):
            house_num = str(i + 1)
            name_val = model.evaluate(name_vars[i]).as_long()
            genre_val = model.evaluate(genre_vars[i]).as_long()
            rows.append([house_num, name_map[name_val], genre_map[genre_val]])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "BookGenre"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()