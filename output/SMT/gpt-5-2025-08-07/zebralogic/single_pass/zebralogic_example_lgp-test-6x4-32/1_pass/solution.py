# Requires: z3-solver (pip install z3-solver)
from z3 import Solver, Int, Distinct, And, Or, If, sat
import json

def solve_puzzle():
    houses = range(1, 7)

    # Categories and values
    Names = ['Eric', 'Alice', 'Arnold', 'Carol', 'Peter', 'Bob']
    Styles = ['mediterranean', 'modern', 'craftsman', 'ranch', 'colonial', 'victorian']
    Music = ['country', 'hip hop', 'pop', 'jazz', 'classical', 'rock']
    Hobbies = ['cooking', 'painting', 'photography', 'woodworking', 'gardening', 'knitting']

    # Create Z3 variables: position of each value (1..6)
    pos_name = {n: Int(f"pos_name_{n}") for n in Names}
    pos_style = {s: Int(f"pos_style_{s}") for s in Styles}
    pos_music = {m: Int(f"pos_music_{m.replace(' ', '_')}") for m in Music}
    pos_hobby = {h: Int(f"pos_hobby_{h}") for h in Hobbies}

    s = Solver()

    # Domains
    for d in [pos_name, pos_style, pos_music, pos_hobby]:
        for v in d.values():
            s.add(And(v >= 1, v <= 6))

    # All-different constraints within each category
    s.add(Distinct(*pos_name.values()))
    s.add(Distinct(*pos_style.values()))
    s.add(Distinct(*pos_music.values()))
    s.add(Distinct(*pos_hobby.values()))

    # Helper abs since Z3's Abs may not be available in all contexts
    def zabs(x):
        return If(x >= 0, x, -x)

    # Clues:
    # 1. Rock music is in the fifth house.
    s.add(pos_music['rock'] == 5)
    # 2. Classical music and the woodworking hobbyist are next to each other.
    s.add(zabs(pos_music['classical'] - pos_hobby['woodworking']) == 1)
    # 3. Mediterranean-style villa is the person who loves hip-hop music.
    s.add(pos_style['mediterranean'] == pos_music['hip hop'])
    # 4. Two houses between Arnold and the person in a Victorian house. (distance 3)
    s.add(zabs(pos_name['Arnold'] - pos_style['victorian']) == 3)
    # 5. Jazz is directly left of Eric.
    s.add(pos_music['jazz'] == pos_name['Eric'] - 1)
    # 6. Hip-hop is somewhere to the left of knitting.
    s.add(pos_music['hip hop'] < pos_hobby['knitting'])
    # 7. Carol is the person who loves hip-hop music.
    s.add(pos_name['Carol'] == pos_music['hip hop'])
    # 8. Craftsman-style house is Arnold.
    s.add(pos_style['craftsman'] == pos_name['Arnold'])
    # 9. Ranch-style home is Eric.
    s.add(pos_style['ranch'] == pos_name['Eric'])
    # 10. Woodworking hobbyist is the person residing in a Victorian house.
    s.add(pos_hobby['woodworking'] == pos_style['victorian'])
    # 11. Country music is in the first house.
    s.add(pos_music['country'] == 1)
    # 12. One house between the painter and the colonial-style house. (distance 2)
    s.add(zabs(pos_hobby['painting'] - pos_style['colonial']) == 2)
    # 13. Alice is the photography enthusiast.
    s.add(pos_name['Alice'] == pos_hobby['photography'])
    # 14. Gardening is Eric.
    s.add(pos_hobby['gardening'] == pos_name['Eric'])
    # 15. Bob is in the third house.
    s.add(pos_name['Bob'] == 3)

    assert s.check() == sat
    m = s.model()

    # Build solution rows
    header = ["House", "Name", "HouseStyle", "MusicGenre", "Hobby"]
    rows = []
    for h in houses:
        # Find which value is at house h
        name_at_h = next(n for n, v in pos_name.items() if m[v].as_long() == h)
        style_at_h = next(st for st, v in pos_style.items() if m[v].as_long() == h)
        music_at_h = next(mu for mu, v in pos_music.items() if m[v].as_long() == h).replace('_', ' ')
        hobby_at_h = next(ho for ho, v in pos_hobby.items() if m[v].as_long() == h)
        rows.append([str(h), name_at_h, style_at_h, music_at_h, hobby_at_h])

    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))