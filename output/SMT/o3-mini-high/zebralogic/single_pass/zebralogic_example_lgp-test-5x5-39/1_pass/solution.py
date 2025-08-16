from z3 import *

def solve():
    s = Solver()
    n = 5

    # Create 5 variables for each house attribute.
    names = [Int(f"name_{i}") for i in range(n)]
    birth = [Int(f"birth_{i}") for i in range(n)]
    mothers = [Int(f"mother_{i}") for i in range(n)]
    occ = [Int(f"occ_{i}") for i in range(n)]
    hair = [Int(f"hair_{i}") for i in range(n)]

    # Each variable is in the domain 0..4.
    for var in names + birth + mothers + occ + hair:
        s.add(And(var >= 0, var < n))

    # Each attribute is a permutation.
    s.add(Distinct(names))
    s.add(Distinct(birth))
    s.add(Distinct(mothers))
    s.add(Distinct(occ))
    s.add(Distinct(hair))

    # --- Define our mappings ---
    # Names mapping: 0: Alice, 1: Eric, 2: Bob, 3: Peter, 4: Arnold.
    ALICE  = 0
    ERIC   = 1
    BOB    = 2
    PETER  = 3
    ARNOLD = 4

    # Birthdays mapping: 0: mar, 1: april, 2: sept, 3: feb, 4: jan.
    MAR   = 0
    APRIL = 1
    SEPT  = 2
    FEB   = 3
    JAN   = 4

    # Mothers mapping: 0: Kailyn, 1: Janelle, 2: Holly, 3: Penny, 4: Aniya.
    KAILYN  = 0
    JANELLE = 1
    HOLLY   = 2
    PENNY   = 3
    ANIYA   = 4

    # Occupations mapping: 0: teacher, 1: doctor, 2: engineer, 3: lawyer, 4: artist.
    TEACHER  = 0
    DOCTOR   = 1
    ENGINEER = 2
    LAWYER   = 3
    ARTIST   = 4

    # Hair mapping: 0: red, 1: black, 2: blonde, 3: brown, 4: gray.
    RED    = 0
    BLACK  = 1
    BLONDE = 2
    BROWN  = 3
    GRAY   = 4

    # --- Add constraints based on the clues ---

    # 1. The person whose birthday is in March is in the fifth house.
    s.add(birth[4] == MAR)

    # 2. The person whose birthday is in February is in the first house.
    s.add(birth[0] == FEB)

    # 3. The person who is a doctor is Eric.
    for i in range(n):
        s.add(Implies(names[i] == ERIC, occ[i] == DOCTOR))

    # 4. The person whose mother's name is Janelle is in the third house.
    s.add(mothers[2] == JANELLE)

    # 5. The person who is an artist is the person who has brown hair.
    for i in range(n):
        s.add(Implies(occ[i] == ARTIST, hair[i] == BROWN))
        s.add(Implies(hair[i] == BROWN, occ[i] == ARTIST))

    # 6. The person who is an artist is in the fourth house.
    s.add(occ[3] == ARTIST)

    # 7. The person whose mother's name is Penny is somewhere to the left of the person who has black hair.
    for i in range(n):
        for j in range(n):
            s.add(Implies(And(mothers[i] == PENNY, hair[j] == BLACK), i < j))

    # 8. Peter is the person who has black hair.
    for i in range(n):
        s.add(Implies(names[i] == PETER, hair[i] == BLACK))

    # 9. The person who has gray hair is the person who is a teacher.
    for i in range(n):
        s.add(Implies(hair[i] == GRAY, occ[i] == TEACHER))
        s.add(Implies(occ[i] == TEACHER, hair[i] == GRAY))

    # 10. Alice is the person whose mother's name is Kailyn.
    for i in range(n):
        s.add(Implies(names[i] == ALICE, mothers[i] == KAILYN))

    # 11. Arnold is somewhere to the right of the person whose birthday is in September.
    for i in range(n):
        for j in range(n):
            s.add(Implies(And(birth[i] == SEPT, names[j] == ARNOLD), i < j))

    # 12. The person who has brown hair is the person whose birthday is in January.
    for i in range(n):
        s.add(Implies(hair[i] == BROWN, birth[i] == JAN))
        s.add(Implies(birth[i] == JAN, hair[i] == BROWN))

    # 13. Arnold is the person who has blonde hair.
    for i in range(n):
        s.add(Implies(names[i] == ARNOLD, hair[i] == BLONDE))

    # 14. The person whose mother's name is Holly is the person who has black hair.
    for i in range(n):
        s.add(Implies(mothers[i] == HOLLY, hair[i] == BLACK))
        s.add(Implies(hair[i] == BLACK, mothers[i] == HOLLY))

    # 15. Peter is the person who is a lawyer.
    for i in range(n):
        s.add(Implies(names[i] == PETER, occ[i] == LAWYER))

    # 16. The person whose birthday is in September is somewhere to the left of the person whose mother's name is Kailyn.
    for i in range(n):
        for j in range(n):
            s.add(Implies(And(birth[i] == SEPT, mothers[j] == KAILYN), i < j))

    # 17. Alice is the person who has gray hair.
    for i in range(n):
        s.add(Implies(names[i] == ALICE, hair[i] == GRAY))

    # --- Solve the puzzle ---
    if s.check() == sat:
        m = s.model()
        # Define string representations for the integer codes.
        names_str = ["Alice", "Eric", "Bob", "Peter", "Arnold"]
        birthdays_str = ["mar", "april", "sept", "feb", "jan"]
        mothers_str = ["Kailyn", "Janelle", "Holly", "Penny", "Aniya"]
        occupations_str = ["teacher", "doctor", "engineer", "lawyer", "artist"]
        hair_str = ["red", "black", "blonde", "brown", "gray"]

        rows = []
        # Houses are numbered 1 to 5 (left-to-right corresponds to list indices 0-4).
        for i in range(n):
            row = [
                str(i+1),
                names_str[m.evaluate(names[i]).as_long()],
                birthdays_str[m.evaluate(birth[i]).as_long()],
                mothers_str[m.evaluate(mothers[i]).as_long()],
                occupations_str[m.evaluate(occ[i]).as_long()],
                hair_str[m.evaluate(hair[i]).as_long()]
            ]
            rows.append(row)
            
        import json
        solution = {
            "solution": {
                "header": ["House", "Name", "Birthday", "Mother", "Occupation", "HairColor"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    solve()