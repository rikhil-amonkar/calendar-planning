import json
from z3 import Solver, Int, Distinct, Or

def solve_puzzle():
    houses = range(1, 7)

    # Attributes
    Names = ['Eric', 'Alice', 'Arnold', 'Carol', 'Peter', 'Bob']
    HouseStyles = ['mediterranean', 'modern', 'craftsman', 'ranch', 'colonial', 'victorian']
    MusicGenres = ['country', 'hip hop', 'pop', 'jazz', 'classical', 'rock']
    Hobbies = ['cooking', 'painting', 'photography', 'woodworking', 'gardening', 'knitting']

    # Create position variables for each attribute
    name_pos = {n: Int(f"name_{n}") for n in Names}
    style_pos = {s: Int(f"style_{s}") for s in HouseStyles}
    music_pos = {m: Int(f"music_{m}") for m in MusicGenres}
    hobby_pos = {h: Int(f"hobby_{h}") for h in Hobbies}

    s = Solver()

    # Domains: all positions 1..6
    for d in [name_pos, style_pos, music_pos, hobby_pos]:
        for v in d.values():
            s.add(Or([v == i for i in houses]))

    # Uniqueness within each category
    s.add(Distinct([name_pos[n] for n in Names]))
    s.add(Distinct([style_pos[h] for h in HouseStyles]))
    s.add(Distinct([music_pos[m] for m in MusicGenres]))
    s.add(Distinct([hobby_pos[h] for h in Hobbies]))

    # Helper constraints
    def next_to(a, b):
        return Or(a == b + 1, a == b - 1)

    def diff_n(a, b, n):
        return Or(a == b + n, a == b - n)

    # Clues:
    # 1. The person who loves rock music is in the fifth house.
    s.add(music_pos['rock'] == 5)

    # 2. The person who loves classical music and the woodworking hobbyist are next to each other.
    s.add(next_to(music_pos['classical'], hobby_pos['woodworking']))

    # 3. The person in a Mediterranean-style villa is the person who loves hip-hop music.
    s.add(style_pos['mediterranean'] == music_pos['hip hop'])

    # 4. There are two houses between Arnold and the person residing in a Victorian house.
    s.add(diff_n(name_pos['Arnold'], style_pos['victorian'], 3))

    # 5. The person who loves jazz music is directly left of Eric.
    s.add(music_pos['jazz'] + 1 == name_pos['Eric'])

    # 6. The person who loves hip-hop music is somewhere to the left of the person who enjoys knitting.
    s.add(music_pos['hip hop'] < hobby_pos['knitting'])

    # 7. Carol is the person who loves hip-hop music.
    s.add(name_pos['Carol'] == music_pos['hip hop'])

    # 8. The person in a Craftsman-style house is Arnold.
    s.add(style_pos['craftsman'] == name_pos['Arnold'])

    # 9. The person in a ranch-style home is Eric.
    s.add(style_pos['ranch'] == name_pos['Eric'])

    # 10. The woodworking hobbyist is the person residing in a Victorian house.
    s.add(hobby_pos['woodworking'] == style_pos['victorian'])

    # 11. The person who loves country music is in the first house.
    s.add(music_pos['country'] == 1)

    # 12. There is one house between the person who paints as a hobby and the person living in a colonial-style house.
    s.add(diff_n(hobby_pos['painting'], style_pos['colonial'], 2))

    # 13. Alice is the photography enthusiast.
    s.add(name_pos['Alice'] == hobby_pos['photography'])

    # 14. The person who enjoys gardening is Eric.
    s.add(hobby_pos['gardening'] == name_pos['Eric'])

    # 15. Bob is in the third house.
    s.add(name_pos['Bob'] == 3)

    if s.check() != 1:  # 1 is sat
        # Fallback empty solution
        output = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "MusicGenre", "Hobby"],
                "rows": []
            }
        }
        print(json.dumps(output, ensure_ascii=False))
        return

    m = s.model()

    # Invert mappings: position -> attribute
    def invert(d):
        inv = {}
        for k, v in d.items():
            inv[m.eval(v).as_long()] = k
        return inv

    inv_names = invert(name_pos)
    inv_styles = invert(style_pos)
    inv_music = invert(music_pos)
    inv_hobbies = invert(hobby_pos)

    rows = []
    for i in sorted(houses):
        rows.append([
            str(i),
            inv_names[i],
            inv_styles[i],
            inv_music[i],
            inv_hobbies[i]
        ])

    output = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "MusicGenre", "Hobby"],
            "rows": rows
        }
    }
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()