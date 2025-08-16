import json
from z3 import Solver, Int, Distinct, And, Or, Implies

def solve_puzzle():
    # Enumerations
    Names = ["Peter", "Arnold", "Eric", "Alice"]
    Flowers = ["daffodils", "carnations", "roses", "lilies"]
    Heights = ["very short", "short", "tall", "average"]
    Mothers = ["Janelle", "Kailyn", "Holly", "Aniya"]
    Occupations = ["engineer", "doctor", "teacher", "artist"]
    Sports = ["swimming", "basketball", "tennis", "soccer"]

    # Indices
    PETER, ARNOLD, ERIC, ALICE = [Names.index(n) for n in Names]
    DAFF, CARN, ROSE, LILY = [Flowers.index(f) for f in Flowers]
    VSHORT, SHORT, TALL, AVG = [Heights.index(h) for h in Heights]
    JANELLE, KAILYN, HOLLY, ANIYA = [Mothers.index(m) for m in Mothers]
    ENG, DOC, TEACH, ART = [Occupations.index(o) for o in Occupations]
    SWIM, BASK, TENN, SOCC = [Sports.index(s) for s in Sports]

    # Variables for each house (0..3 represent houses 1..4)
    Name = [Int(f"Name_{i}") for i in range(4)]
    Flower = [Int(f"Flower_{i}") for i in range(4)]
    Height = [Int(f"Height_{i}") for i in range(4)]
    Mother = [Int(f"Mother_{i}") for i in range(4)]
    Occupation = [Int(f"Occupation_{i}") for i in range(4)]
    Sport = [Int(f"Sport_{i}") for i in range(4)]

    s = Solver()

    # Domains: each attribute is 0..3
    for arr in [Name, Flower, Height, Mother, Occupation, Sport]:
        for v in arr:
            s.add(v >= 0, v <= 3)

    # Uniqueness across houses for each category
    s.add(Distinct(Name))
    s.add(Distinct(Flower))
    s.add(Distinct(Height))
    s.add(Distinct(Mother))
    s.add(Distinct(Occupation))
    s.add(Distinct(Sport))

    # Clues
    # 1. Swimming <-> Roses
    for i in range(4):
        s.add(And(Implies(Sport[i] == SWIM, Flower[i] == ROSE),
                  Implies(Flower[i] == ROSE, Sport[i] == SWIM)))

    # 2. Roses <-> Eric
    for i in range(4):
        s.add(And(Implies(Flower[i] == ROSE, Name[i] == ERIC),
                  Implies(Name[i] == ERIC, Flower[i] == ROSE)))

    # 3. Arnold is tall
    for i in range(4):
        s.add(Implies(Name[i] == ARNOLD, Height[i] == TALL))

    # 4. Daffodils is somewhere to the right of the engineer
    s.add(Implies(Occupation[0] == ENG, Or(Flower[1] == DAFF, Flower[2] == DAFF, Flower[3] == DAFF)))
    s.add(Implies(Occupation[1] == ENG, Or(Flower[2] == DAFF, Flower[3] == DAFF)))
    s.add(Implies(Occupation[2] == ENG, Flower[3] == DAFF))
    s.add(Occupation[3] != ENG)  # cannot have daffodils to the right of house 4

    # 5. Soccer <-> Short
    for i in range(4):
        s.add(And(Implies(Sport[i] == SOCC, Height[i] == SHORT),
                  Implies(Height[i] == SHORT, Sport[i] == SOCC)))

    # 6. Teacher is in the first house
    s.add(Occupation[0] == TEACH)

    # 7. Janelle <-> Carnations
    for i in range(4):
        s.add(And(Implies(Mother[i] == JANELLE, Flower[i] == CARN),
                  Implies(Flower[i] == CARN, Mother[i] == JANELLE)))

    # 8. Basketball <-> Average
    for i in range(4):
        s.add(And(Implies(Sport[i] == BASK, Height[i] == AVG),
                  Implies(Height[i] == AVG, Sport[i] == BASK)))

    # 9. Arnold is not in the third house (house index 2)
    s.add(Name[2] != ARNOLD)

    # 10. Holly is somewhere to the right of the average height
    s.add(Implies(Height[0] == AVG, Or(Mother[1] == HOLLY, Mother[2] == HOLLY, Mother[3] == HOLLY)))
    s.add(Implies(Height[1] == AVG, Or(Mother[2] == HOLLY, Mother[3] == HOLLY)))
    s.add(Implies(Height[2] == AVG, Mother[3] == HOLLY))
    s.add(Height[3] != AVG)  # cannot have someone to the right of house 4

    # 11. Peter <-> Doctor
    for i in range(4):
        s.add(And(Implies(Name[i] == PETER, Occupation[i] == DOC),
                  Implies(Occupation[i] == DOC, Name[i] == PETER)))

    # 12. Aniya <-> Alice
    for i in range(4):
        s.add(And(Implies(Mother[i] == ANIYA, Name[i] == ALICE),
                  Implies(Name[i] == ALICE, Mother[i] == ANIYA)))

    # 13. Arnold <-> Lilies
    for i in range(4):
        s.add(And(Implies(Name[i] == ARNOLD, Flower[i] == LILY),
                  Implies(Flower[i] == LILY, Name[i] == ARNOLD)))

    if s.check() != z3.sat:
        raise RuntimeError("No solution found")

    m = s.model()

    def val(arr, i, values):
        return values[m.evaluate(arr[i]).as_long()]

    rows = []
    for i in range(4):
        rows.append([
            str(i + 1),
            val(Name, i, Names),
            val(Flower, i, Flowers),
            val(Height, i, Heights),
            val(Mother, i, Mothers),
            val(Occupation, i, Occupations),
            val(Sport, i, Sports),
        ])

    output = {
        "solution": {
            "header": ["House", "Name", "Flower", "Height", "Mother", "Occupation", "FavoriteSport"],
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    # Ensure z3 is available
    import z3
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))