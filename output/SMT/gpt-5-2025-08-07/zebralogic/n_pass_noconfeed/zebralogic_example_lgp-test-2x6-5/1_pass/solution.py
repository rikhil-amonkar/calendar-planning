import json
from z3 import Int, Solver, Distinct, And, Or, Abs

def solve_puzzle():
    # Houses
    houses = [1, 2]

    # Attributes
    Names = ["Arnold", "Eric"]
    Occupations = ["engineer", "doctor"]
    Birthdays = ["april", "sept"]
    HouseStyles = ["victorian", "colonial"]
    Heights = ["very short", "short"]
    Cigars = ["pall mall", "prince"]

    # Create Z3 variables mapping each attribute value to a house number
    def mk_vars(values, prefix):
        return {v: Int(f"{prefix}_{v.replace(' ', '_')}") for v in values}

    name_pos = mk_vars(Names, "name")
    occ_pos = mk_vars(Occupations, "occ")
    bday_pos = mk_vars(Birthdays, "bday")
    style_pos = mk_vars(HouseStyles, "style")
    height_pos = mk_vars(Heights, "height")
    cigar_pos = mk_vars(Cigars, "cigar")

    s = Solver()

    # Domain constraints: each variable is in 1..2
    def in_domain(d):
        for v in d.values():
            s.add(Or(*[v == h for h in houses]))

    in_domain(name_pos)
    in_domain(occ_pos)
    in_domain(bday_pos)
    in_domain(style_pos)
    in_domain(height_pos)
    in_domain(cigar_pos)

    # Uniqueness constraints: each attribute's values occupy different houses
    s.add(Distinct(*name_pos.values()))
    s.add(Distinct(*occ_pos.values()))
    s.add(Distinct(*bday_pos.values()))
    s.add(Distinct(*style_pos.values()))
    s.add(Distinct(*height_pos.values()))
    s.add(Distinct(*cigar_pos.values()))

    # Clues:
    # 1. The person who is an engineer is in the first house.
    s.add(occ_pos["engineer"] == 1)

    # 2. The person whose birthday is in April and the person who is a doctor are next to each other.
    s.add(Abs(bday_pos["april"] - occ_pos["doctor"]) == 1)

    # 3. The person living in a colonial-style house is the person who is an engineer.
    s.add(style_pos["colonial"] == occ_pos["engineer"])

    # 4. The person who is very short is the person who is an engineer.
    s.add(height_pos["very short"] == occ_pos["engineer"])

    # 5. The person who is short is the person partial to Pall Mall.
    s.add(height_pos["short"] == cigar_pos["pall mall"])

    # 6. The person who is an engineer is Eric.
    s.add(occ_pos["engineer"] == name_pos["Eric"])

    if s.check() != 1:  # 1 corresponds to sat
        raise RuntimeError("Puzzle is unsatisfiable")

    m = s.model()

    # Build reverse mappings: house -> attribute value
    def house_to_value(pos_dict):
        rev = {}
        for val, var in pos_dict.items():
            rev[m[var].as_long()] = val
        return rev

    name_at = house_to_value(name_pos)
    occ_at = house_to_value(occ_pos)
    bday_at = house_to_value(bday_pos)
    style_at = house_to_value(style_pos)
    height_at = house_to_value(height_pos)
    cigar_at = house_to_value(cigar_pos)

    # Prepare JSON output
    header = ["House", "Name", "Occupation", "Birthday", "HouseStyle", "Height", "Cigar"]
    rows = []
    for h in houses:
        rows.append([
            str(h),
            name_at[h],
            occ_at[h],
            bday_at[h],
            style_at[h],
            height_at[h],
            cigar_at[h],
        ])

    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    res = solve_puzzle()
    print(json.dumps(res, ensure_ascii=False))