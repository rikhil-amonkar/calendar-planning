import json
from z3 import Solver, Int, And, Distinct, sat

def solve_puzzle():
    # Houses
    houses = [1, 2]

    # Attributes
    Names = ["Arnold", "Eric"]
    HairColors = ["black", "brown"]
    FavoriteSports = ["basketball", "soccer"]
    Smoothies = ["desert", "cherry"]

    # Create Z3 variables: position (house index) for each attribute value
    name_pos = {n: Int(f"pos_name_{n}") for n in Names}
    hair_pos = {h: Int(f"pos_hair_{h}") for h in HairColors}
    sport_pos = {s: Int(f"pos_sport_{s}") for s in FavoriteSports}
    smoothie_pos = {sm: Int(f"pos_smoothie_{sm}") for sm in Smoothies}

    s = Solver()

    # Domain constraints: each position is a house number
    for d in [name_pos, hair_pos, sport_pos, smoothie_pos]:
        for v in d.values():
            s.add(And(v >= houses[0], v <= houses[-1]))

    # Uniqueness within each category
    s.add(Distinct([name_pos[n] for n in Names]))
    s.add(Distinct([hair_pos[h] for h in HairColors]))
    s.add(Distinct([sport_pos[sp] for sp in FavoriteSports]))
    s.add(Distinct([smoothie_pos[sm] for sm in Smoothies]))

    # Clue 1: The Desert smoothie lover is Arnold.
    s.add(smoothie_pos["desert"] == name_pos["Arnold"])

    # Clue 2: The person who has brown hair is the person who loves basketball.
    s.add(hair_pos["brown"] == sport_pos["basketball"])

    # Clue 3: Arnold is somewhere to the left of the person who has black hair.
    s.add(name_pos["Arnold"] < hair_pos["black"])

    res = s.check()
    if res != sat:
        # Provide a clearer error in case of unknown/unsat
        reason = s.reason_unknown() if str(res) == "unknown" else "unsatisfiable"
        raise RuntimeError(f"Puzzle is {reason}.")

    m = s.model()

    # Build solution rows sorted by house index
    rows = []
    for h in houses:
        # Find attribute value whose position equals the current house
        name = next(n for n in Names if m.evaluate(name_pos[n]).as_long() == h)
        hair = next(col for col in HairColors if m.evaluate(hair_pos[col]).as_long() == h)
        sport = next(sp for sp in FavoriteSports if m.evaluate(sport_pos[sp]).as_long() == h)
        smoothie = next(sm for sm in Smoothies if m.evaluate(smoothie_pos[sm]).as_long() == h)

        rows.append([str(h), name, hair, sport, smoothie])

    output = {
        "solution": {
            "header": ["House", "Name", "HairColor", "FavoriteSport", "Smoothie"],
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False, indent=2))