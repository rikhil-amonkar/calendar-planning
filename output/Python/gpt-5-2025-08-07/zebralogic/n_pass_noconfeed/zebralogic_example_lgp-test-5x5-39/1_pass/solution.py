import json
from itertools import permutations

def solve():
    houses = [1, 2, 3, 4, 5]

    Names = ["Alice", "Eric", "Bob", "Peter", "Arnold"]
    Birthdays = ["mar", "april", "sept", "feb", "jan"]
    Mothers = ["Holly", "Janelle", "Kailyn", "Penny", "Aniya"]
    Occupations = ["engineer", "doctor", "lawyer", "artist", "teacher"]
    HairColors = ["red", "blonde", "black", "gray", "brown"]

    solution = None

    # Iterate over all possible name placements with early pruning from constraints
    for perm in permutations(Names):
        # perm[i] is the Name in house i+1

        # From combined constraints:
        # - House 4 is the artist (C6), artist has brown hair (C5), brown hair is Jan (C12)
        #   Peter (black hair, lawyer), Arnold (blonde hair), Alice (gray hair), Eric (doctor) cannot be in house 4 => Bob must be in house 4
        if perm[3] != "Bob":
            continue

        # Peter cannot be in house 1 (C7 requires Penny somewhere left of black hair),
        # cannot be in house 3 (C4 mother Janelle fixed at 3 but Peter's mother is Holly from C14),
        # and not in house 4 (artist at 4 but Peter is lawyer from C15)
        if perm[0] == "Peter" or perm[2] == "Peter":
            continue

        # Alice cannot be in house 1 (C16 sept left of Kailyn/Alice), nor 3 (C4 vs C10), nor 4 (brown hair at 4 but Alice has gray hair C17)
        if perm[0] == "Alice" or perm[2] == "Alice":
            continue

        name_pos = {name: i + 1 for i, name in enumerate(perm)}  # name -> house

        # Birthdays: C1 mar=5, C2 feb=1, and from C12 & C6 & C5, jan=4
        # Remaining birthdays 'april' and 'sept' occupy houses 2 and 3 in some order
        for sept_house, april_house in [(2, 3), (3, 2)]:
            bday_pos = {
                "mar": 5,
                "feb": 1,
                "jan": 4,
                "sept": sept_house,
                "april": april_house,
            }

            # C11 Arnold right of September
            if not (name_pos["Arnold"] > bday_pos["sept"]):
                continue

            # C16 September is left of Kailyn (Alice) (C10)
            if not (bday_pos["sept"] < name_pos["Alice"]):
                continue

            # Hair colors:
            # C8 Peter has black hair
            # C13 Arnold has blonde hair
            # C17 Alice has gray hair
            # C5 & C6 -> brown hair is at house 4 (artist)
            hair_pos = {}
            hair_pos["black"] = name_pos["Peter"]
            hair_pos["blonde"] = name_pos["Arnold"]
            hair_pos["gray"] = name_pos["Alice"]
            hair_pos["brown"] = 4
            # Remaining red hair is the only unused house
            used_hair_houses = set(hair_pos.values())
            red_house = next(h for h in houses if h not in used_hair_houses)
            hair_pos["red"] = red_house

            # Mothers:
            # C4 Janelle is in house 3
            # C14 Holly is in the black hair person's house (Peter's house)
            # C10 Kailyn is Alice's house
            mother_pos = {}
            mother_pos["Janelle"] = 3
            mother_pos["Holly"] = hair_pos["black"]
            mother_pos["Kailyn"] = name_pos["Alice"]

            remaining_mother_houses = [h for h in houses if h not in {mother_pos["Janelle"], mother_pos["Holly"], mother_pos["Kailyn"]}]
            # Assign Penny and Aniya to remaining two houses with C7: Penny left of black hair
            for penny_house in remaining_mother_houses:
                if not (penny_house < hair_pos["black"]):
                    continue
                aniya_house = next(h for h in remaining_mother_houses if h != penny_house)
                mother_pos["Penny"] = penny_house
                mother_pos["Aniya"] = aniya_house

                # Occupations:
                # C6 artist = 4
                # C15 Peter = lawyer
                # C3 Eric = doctor
                # C9 gray hair = teacher (and from C17 gray hair is Alice -> Alice is teacher)
                occup_pos = {}
                occup_pos["artist"] = 4
                occup_pos["lawyer"] = name_pos["Peter"]
                occup_pos["doctor"] = name_pos["Eric"]
                occup_pos["teacher"] = hair_pos["gray"]
                used_occ_houses = {occup_pos["artist"], occup_pos["lawyer"], occup_pos["doctor"], occup_pos["teacher"]}
                engineer_house = next(h for h in houses if h not in used_occ_houses)
                occup_pos["engineer"] = engineer_house

                # Final validation of all constraints
                ok = True
                ok &= (bday_pos["mar"] == 5)  # C1
                ok &= (bday_pos["feb"] == 1)  # C2
                ok &= (occup_pos["doctor"] == name_pos["Eric"])  # C3
                ok &= (mother_pos["Janelle"] == 3)  # C4
                ok &= (occup_pos["artist"] == hair_pos["brown"])  # C5
                ok &= (occup_pos["artist"] == 4)  # C6
                ok &= (mother_pos["Penny"] < hair_pos["black"])  # C7
                ok &= (name_pos["Peter"] == hair_pos["black"])  # C8
                ok &= (hair_pos["gray"] == occup_pos["teacher"])  # C9
                ok &= (name_pos["Alice"] == mother_pos["Kailyn"])  # C10
                ok &= (name_pos["Arnold"] > bday_pos["sept"])  # C11
                ok &= (hair_pos["brown"] == bday_pos["jan"])  # C12
                ok &= (name_pos["Arnold"] == hair_pos["blonde"])  # C13
                ok &= (mother_pos["Holly"] == hair_pos["black"])  # C14
                ok &= (name_pos["Peter"] == occup_pos["lawyer"])  # C15
                ok &= (bday_pos["sept"] < mother_pos["Kailyn"])  # C16 (same as < Alice's house)
                ok &= (name_pos["Alice"] == hair_pos["gray"])  # C17

                if not ok:
                    continue

                # Build house -> attribute reverse maps
                house_to_name = {house: name for name, house in name_pos.items()}
                house_to_bday = {house: bday for bday, house in bday_pos.items()}
                house_to_mother = {house: mom for mom, house in mother_pos.items()}
                house_to_occup = {house: occ for occ, house in occup_pos.items()}
                house_to_hair = {house: hair for hair, house in hair_pos.items()}

                rows = []
                for h in houses:
                    rows.append([
                        str(h),
                        house_to_name[h],
                        house_to_bday[h],
                        house_to_mother[h],
                        house_to_occup[h],
                        house_to_hair[h],
                    ])

                solution = {
                    "solution": {
                        "header": ["House", "Name", "Birthday", "Mother", "Occupation", "HairColor"],
                        "rows": rows
                    }
                }
                return solution

    return None

def main():
    result = solve()
    if result is None:
        print(json.dumps({"error": "No solution found"}))
    else:
        print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()