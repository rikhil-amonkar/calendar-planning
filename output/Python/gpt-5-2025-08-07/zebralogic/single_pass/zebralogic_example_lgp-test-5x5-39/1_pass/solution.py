import itertools
import json

def solve():
    houses = list(range(5))  # indices 0..4 map to houses 1..5

    Names = ["Alice", "Eric", "Bob", "Peter", "Arnold"]
    Birthdays = ["mar", "april", "sept", "feb", "jan"]
    Mothers = ["Holly", "Janelle", "Kailyn", "Penny", "Aniya"]
    Occupations = ["engineer", "doctor", "lawyer", "artist", "teacher"]
    HairColors = ["red", "blonde", "black", "gray", "brown"]

    # Helper to set a value if consistent
    def set_val(arr, idx, val):
        if arr[idx] is None or arr[idx] == val:
            arr[idx] = val
            return True
        return False

    # Build possible birthday assignments given fixed info:
    # 1) mar in house 5 (index 4)
    # 2) feb in house 1 (index 0)
    # 6+5+12 => artist in house 4 (index 3) has brown hair and Jan birthday -> jan in house 4
    birthday_options = []
    fixed_birthdays = [None]*5
    fixed_birthdays[0] = "feb"
    fixed_birthdays[4] = "mar"
    fixed_birthdays[3] = "jan"
    remaining_months = ["april", "sept"]
    for perm in itertools.permutations(remaining_months):
        b = fixed_birthdays[:]
        b[1] = perm[0]
        b[2] = perm[1]
        birthday_options.append(b)

    solution = None

    for birthdays in birthday_options:
        house_of_sept = birthdays.index("sept")

        # Try all assignments of names to houses
        for name_assignment in itertools.permutations(Names):
            idx_Alice = name_assignment.index("Alice")
            idx_Eric = name_assignment.index("Eric")
            idx_Bob = name_assignment.index("Bob")
            idx_Peter = name_assignment.index("Peter")
            idx_Arnold = name_assignment.index("Arnold")

            # 11) Arnold is to the right of the person whose birthday is in September
            if not (idx_Arnold > house_of_sept):
                continue

            # Hair assignment based on constraints:
            hair = [None]*5
            # 8) Peter has black hair
            if not set_val(hair, idx_Peter, "black"):
                continue
            # 17) Alice has gray hair
            if not set_val(hair, idx_Alice, "gray"):
                continue
            # 13) Arnold has blonde hair
            if not set_val(hair, idx_Arnold, "blonde"):
                continue
            # 5 & 6) Artist is brown hair, and artist is in the fourth house -> brown hair in house 4 (index 3)
            if not set_val(hair, 3, "brown"):
                continue

            # Fill the remaining hair color (red) in the last unfilled house
            remaining_houses_for_hair = [i for i, v in enumerate(hair) if v is None]
            if len(remaining_houses_for_hair) != 1:
                continue
            if not set_val(hair, remaining_houses_for_hair[0], "red"):
                continue

            # 12) Brown hair <-> January birthday
            for i in houses:
                if hair[i] == "brown" and birthdays[i] != "jan":
                    break
                if birthdays[i] == "jan" and hair[i] != "brown":
                    break
            else:
                pass  # ok
                # continue if broke
                # but we need to ensure loop didn't break
                # We'll use a flag
                brown_jan_ok = True
            # Re-check correctness of the above loop (since break doesn't have label)
            brown_jan_ok = True
            for i in houses:
                if hair[i] == "brown" and birthdays[i] != "jan":
                    brown_jan_ok = False
                    break
                if birthdays[i] == "jan" and hair[i] != "brown":
                    brown_jan_ok = False
                    break
            if not brown_jan_ok:
                continue

            # Occupations:
            occ = [None]*5
            # 6) artist in the fourth house
            if not set_val(occ, 3, "artist"):
                continue
            # 15) Peter is a lawyer
            if not set_val(occ, idx_Peter, "lawyer"):
                continue
            # 3) Doctor is Eric
            if not set_val(occ, idx_Eric, "doctor"):
                continue
            # 9) Gray hair <-> teacher
            # person with gray hair is teacher
            idx_gray = hair.index("gray")
            if not set_val(occ, idx_gray, "teacher"):
                continue
            # Ensure artist is brown hair (5)
            if hair[3] != "brown":
                continue

            # Fill remaining occupation with engineer
            remaining_occ_houses = [i for i, v in enumerate(occ) if v is None]
            if len(remaining_occ_houses) != 1:
                continue
            occ[remaining_occ_houses[0]] = "engineer"

            # Mothers:
            mothers = [None]*5
            # 4) Janelle in third house (index 2)
            if not set_val(mothers, 2, "Janelle"):
                continue
            # 10) Alice's mother is Kailyn
            if not set_val(mothers, idx_Alice, "Kailyn"):
                continue
            # 14) Holly is the black hair person's mother; black hair is Peter
            if not set_val(mothers, idx_Peter, "Holly"):
                continue

            # Assign the remaining mothers: Penny and Aniya
            remaining_mother_houses = [i for i, v in enumerate(mothers) if v is None]
            remaining_mothers = ["Penny", "Aniya"]

            # 16) September is to the left of Kailyn (Alice)
            if not (house_of_sept < idx_Alice):
                continue

            found_mothers = False
            for perm in itertools.permutations(remaining_mothers):
                mothers_trial = mothers[:]
                ok = True
                for h, m in zip(remaining_mother_houses, perm):
                    if not set_val(mothers_trial, h, m):
                        ok = False
                        break
                if not ok:
                    continue
                # 7) Penny is somewhere to the left of black hair (Peter)
                idx_penny = mothers_trial.index("Penny")
                if not (idx_penny < idx_Peter):
                    continue
                # All constraints satisfied
                mothers = mothers_trial
                found_mothers = True
                break

            if not found_mothers:
                continue

            # Final double-checks for bi-directional constraints:
            # 9) gray <-> teacher
            if not (occ[idx_gray] == "teacher" and "teacher" in occ and occ.count("teacher") == 1):
                continue
            # 5) artist <-> brown
            if not (occ[3] == "artist" and hair[3] == "brown"):
                continue
            # 12) brown <-> jan already checked

            # Construct solution
            rows = []
            for i in range(5):
                rows.append([
                    str(i+1),
                    name_assignment[i],
                    birthdays[i],
                    mothers[i],
                    occ[i],
                    hair[i]
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
    print(json.dumps(result, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()