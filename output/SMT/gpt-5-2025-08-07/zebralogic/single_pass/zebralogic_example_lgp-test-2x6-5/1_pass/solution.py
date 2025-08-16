import json
from z3 import Solver, Int, Distinct, And, Or, Implies, sat

def solve_puzzle():
    # Houses
    N = 2
    houses = list(range(N))  # 0-based indexing for Z3 vars; will print as 1..N

    # Domains
    Names = ["Arnold", "Eric"]
    Occupations = ["engineer", "doctor"]
    Birthdays = ["april", "sept"]
    HouseStyles = ["victorian", "colonial"]
    Heights = ["very short", "short"]
    Cigars = ["pall mall", "prince"]

    # Index maps
    NameIdx = {v: i for i, v in enumerate(Names)}
    OccupationIdx = {v: i for i, v in enumerate(Occupations)}
    BirthdayIdx = {v: i for i, v in enumerate(Birthdays)}
    HouseStyleIdx = {v: i for i, v in enumerate(HouseStyles)}
    HeightIdx = {v: i for i, v in enumerate(Heights)}
    CigarIdx = {v: i for i, v in enumerate(Cigars)}

    # Z3 variables per house
    name = [Int(f"name_{i+1}") for i in houses]
    occupation = [Int(f"occupation_{i+1}") for i in houses]
    birthday = [Int(f"birthday_{i+1}") for i in houses]
    housestyle = [Int(f"housestyle_{i+1}") for i in houses]
    height = [Int(f"height_{i+1}") for i in houses]
    cigar = [Int(f"cigar_{i+1}") for i in houses]

    s = Solver()

    # Domain constraints
    def within_domain(vars_list, size):
        for v in vars_list:
            s.add(And(v >= 0, v < size))

    within_domain(name, len(Names))
    within_domain(occupation, len(Occupations))
    within_domain(birthday, len(Birthdays))
    within_domain(housestyle, len(HouseStyles))
    within_domain(height, len(Heights))
    within_domain(cigar, len(Cigars))

    # Uniqueness across houses for each attribute
    s.add(Distinct(name))
    s.add(Distinct(occupation))
    s.add(Distinct(birthday))
    s.add(Distinct(housestyle))
    s.add(Distinct(height))
    s.add(Distinct(cigar))

    # Clues:

    # 1. The person who is an engineer is in the first house.
    s.add(occupation[0] == OccupationIdx["engineer"])

    # 2. The person whose birthday is in April and the person who is a doctor are next to each other.
    for i in houses:
        neighbors = []
        if i - 1 >= 0:
            neighbors.append(i - 1)
        if i + 1 < N:
            neighbors.append(i + 1)
        s.add(Implies(birthday[i] == BirthdayIdx["april"],
                      Or([occupation[j] == OccupationIdx["doctor"] for j in neighbors])))

    # 3. The person living in a colonial-style house is the person who is an engineer.
    for i in houses:
        s.add(And(
            Implies(housestyle[i] == HouseStyleIdx["colonial"], occupation[i] == OccupationIdx["engineer"]),
            Implies(occupation[i] == OccupationIdx["engineer"], housestyle[i] == HouseStyleIdx["colonial"])
        ))

    # 4. The person who is very short is the person who is an engineer.
    for i in houses:
        s.add(And(
            Implies(height[i] == HeightIdx["very short"], occupation[i] == OccupationIdx["engineer"]),
            Implies(occupation[i] == OccupationIdx["engineer"], height[i] == HeightIdx["very short"])
        ))

    # 5. The person who is short is the person partial to Pall Mall.
    for i in houses:
        s.add(And(
            Implies(height[i] == HeightIdx["short"], cigar[i] == CigarIdx["pall mall"]),
            Implies(cigar[i] == CigarIdx["pall mall"], height[i] == HeightIdx["short"])
        ))

    # 6. The person who is an engineer is Eric.
    for i in houses:
        s.add(And(
            Implies(occupation[i] == OccupationIdx["engineer"], name[i] == NameIdx["Eric"]),
            Implies(name[i] == NameIdx["Eric"], occupation[i] == OccupationIdx["engineer"])
        ))

    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()

    # Build the solution rows
    rows = []
    for i in houses:
        row = [
            str(i + 1),
            Names[m[name[i]].as_long()],
            Occupations[m[occupation[i]].as_long()],
            Birthdays[m[birthday[i]].as_long()],
            HouseStyles[m[housestyle[i]].as_long()],
            Heights[m[height[i]].as_long()],
            Cigars[m[cigar[i]].as_long()],
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": ["House", "Name", "Occupation", "Birthday", "HouseStyle", "Height", "Cigar"],
            "rows": rows
        }
    }
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()