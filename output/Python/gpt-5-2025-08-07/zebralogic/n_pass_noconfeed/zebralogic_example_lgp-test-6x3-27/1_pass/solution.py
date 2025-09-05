import itertools
import json

def solve():
    houses = list(range(6))  # indices 0..5 represent houses 1..6
    Names = ["Alice", "Arnold", "Eric", "Peter", "Bob", "Carol"]
    Occupations = ["engineer", "artist", "doctor", "teacher", "nurse", "lawyer"]
    Cars = ["chevrolet silverado", "ford f150", "honda civic", "toyota camry", "bmw 3 series", "tesla model 3"]

    # Utility to check final solution (defensive verification)
    def verify_solution(name_at, occ_at, car_at):
        # All unique checks
        if len(set(name_at)) != 6 or len(set(occ_at)) != 6 or len(set(car_at)) != 6:
            return False

        pos = {name: i for i, name in enumerate(name_at)}
        pos_occ = {occ: i for i, occ in enumerate(occ_at)}
        pos_car = {car: i for i, car in enumerate(car_at)}

        # 1. Ford F-150 is in the fifth house.
        if pos_car["ford f150"] != 4:
            return False
        # 2. Chevrolet Silverado is not in the second house.
        if pos_car["chevrolet silverado"] == 1:
            return False
        # 3. Honda Civic and Peter are next to each other.
        if abs(pos_car["honda civic"] - pos["Peter"]) != 1:
            return False
        # 4. Lawyer is not in the fifth house.
        if pos_occ["lawyer"] == 4:
            return False
        # 5. Nurse is directly left of artist.
        if not (pos_occ["nurse"] + 1 == pos_occ["artist"]):
            return False
        # 6. Carol is somewhere to the right of Eric.
        if not (pos["Carol"] > pos["Eric"]):
            return False
        # 7. Doctor is Eric.
        if pos_occ["doctor"] != pos["Eric"]:
            return False
        # 8. Teacher somewhere left of nurse.
        if not (pos_occ["teacher"] < pos_occ["nurse"]):
            return False
        # 9. Carol is not in the sixth house.
        if pos["Carol"] == 5:
            return False
        # 10. Engineer is Bob.
        if pos_occ["engineer"] != pos["Bob"]:
            return False
        # 11. Toyota Camry is the nurse.
        if pos_car["toyota camry"] != pos_occ["nurse"]:
            return False
        # 12. One house between Peter and lawyer.
        if abs(pos["Peter"] - pos_occ["lawyer"]) != 2:
            return False
        # 13. One house between Tesla and Bob.
        if abs(pos_car["tesla model 3"] - pos["Bob"]) != 2:
            return False
        # 14. Arnold is the artist.
        if pos_occ["artist"] != pos["Arnold"]:
            return False
        return True

    solutions = []

    # Search over permutations of names (720 possibilities)
    for name_perm in itertools.permutations(Names):
        pos = {name: i for i, name in enumerate(name_perm)}

        # Apply name-only constraints early:
        # 6. Carol is somewhere to the right of Eric.
        if not (pos["Carol"] > pos["Eric"]):
            continue
        # 9. Carol is not in the sixth house.
        if pos["Carol"] == 5:
            continue

        # 14. Arnold is the artist, and 5. nurse is directly left of artist
        jA = pos["Arnold"]
        if jA == 0:
            continue  # no house to the left for nurse
        nursePos = jA - 1

        # 11. Camry is nurse and 1. F150 at house 5 => nurse cannot be in house 5
        if nursePos == 4:
            continue  # would conflict with F150 at house 5

        # Build occupation array with partial assignments
        occ_at = [None] * 6
        # 14. Arnold is artist
        occ_at[jA] = "artist"
        # 5. nurse directly left of artist
        if occ_at[nursePos] is not None:
            continue
        occ_at[nursePos] = "nurse"

        # 7. Doctor is Eric
        posEric = pos["Eric"]
        if occ_at[posEric] is not None and occ_at[posEric] != "doctor":
            continue
        if posEric in (jA, nursePos):
            continue  # conflicts with artist/nurse already set
        occ_at[posEric] = "doctor"

        # 10. Engineer is Bob
        posBob = pos["Bob"]
        if occ_at[posBob] is not None and occ_at[posBob] != "engineer":
            continue
        if posBob in (jA, nursePos, posEric):
            continue  # conflicts with existing occupations
        occ_at[posBob] = "engineer"

        # 8. Teacher somewhere left of nurse
        # Teacher must be in any position < nursePos and not occupied yet
        teacher_candidates = [i for i in range(nursePos) if occ_at[i] is None]
        if not teacher_candidates:
            continue

        # 12. One house between Peter and lawyer; 4. Lawyer not in fifth house
        posPeter = pos["Peter"]
        law_positions = set()
        if posPeter - 2 >= 0:
            law_positions.add(posPeter - 2)
        if posPeter + 2 <= 5:
            law_positions.add(posPeter + 2)
        if 4 in law_positions:
            law_positions.remove(4)  # not in house 5
        # Lawyer must be in one of these and unoccupied
        law_positions = [i for i in law_positions if occ_at[i] is None]
        if not law_positions:
            continue

        # Try all combinations for teacher and lawyer placement
        for lawpos in law_positions:
            occ_at2 = occ_at[:]
            occ_at2[lawpos] = "lawyer"

            # Teacher candidates cannot use lawpos anymore
            tcands = [i for i in teacher_candidates if occ_at2[i] is None]
            if not tcands:
                continue

            for tpos in tcands:
                occ_at3 = occ_at2[:]
                occ_at3[tpos] = "teacher"

                # Check that all occupations assigned
                remaining_positions = [i for i, v in enumerate(occ_at3) if v is None]
                remaining_occs = [o for o in Occupations if o not in occ_at3]
                if len(remaining_positions) != len(remaining_occs):
                    continue
                # If any remain, they should be just one position/occ (should not happen often)
                for rp, ro in zip(remaining_positions, remaining_occs):
                    occ_at3[rp] = ro

                # Now assign cars with constraints
                # Build domains for cars
                dom = {}
                # 1. Ford F-150 is in the fifth house.
                dom["ford f150"] = {4}
                # 11. Toyota Camry is the nurse.
                dom["toyota camry"] = {nursePos}
                # 13. One house between Tesla and Bob.
                tes = set()
                if posBob - 2 >= 0:
                    tes.add(posBob - 2)
                if posBob + 2 <= 5:
                    tes.add(posBob + 2)
                dom["tesla model 3"] = tes
                # 3. Honda Civic and Peter are next to each other.
                hon = set()
                if posPeter - 1 >= 0:
                    hon.add(posPeter - 1)
                if posPeter + 1 <= 5:
                    hon.add(posPeter + 1)
                dom["honda civic"] = hon
                # 2. Chevrolet Silverado not in the second house (index 1)
                dom["chevrolet silverado"] = set(range(6)) - {1}
                # BMW unrestricted
                dom["bmw 3 series"] = set(range(6))

                # Early contradiction: ensure Camry and F150 positions don't collide
                if nursePos == 4:
                    continue  # would conflict, but we already prevented earlier

                # Backtracking assignment of cars
                car_models = list(dom.keys())
                car_models.sort(key=lambda m: len(dom[m]))
                car_at = [None] * 6
                used_pos = set()

                def assign_car(idx):
                    if idx == len(car_models):
                        return True
                    m = car_models[idx]
                    for p in sorted(dom[m]):
                        if p in used_pos:
                            continue
                        # No extra car-occupation linkage beyond Camry/nurse (already enforced by domain)
                        car_at[p] = m
                        used_pos.add(p)
                        if assign_car(idx + 1):
                            return True
                        used_pos.remove(p)
                        car_at[p] = None
                    return False

                if not assign_car(0):
                    continue

                # Build result and verify
                name_at = list(name_perm)
                if not verify_solution(name_at, occ_at3, car_at):
                    continue

                # Create rows
                rows = []
                for i in range(6):
                    rows.append([str(i + 1), name_at[i], occ_at3[i], car_at[i]])

                solutions.append({
                    "header": ["House", "Name", "Occupation", "CarModel"],
                    "rows": rows
                })

                # If unique solution is expected, we can return the first one found.
                if solutions:
                    return solutions[0]

    # If no solution found, still return a valid JSON structure with placeholders
    # to satisfy output requirements (though logically, there should be a solution).
    placeholder_rows = [[str(i + 1), "unknown", "unknown", "unknown"] for i in range(6)]
    return {
        "header": ["House", "Name", "Occupation", "CarModel"],
        "rows": placeholder_rows
    }

if __name__ == "__main__":
    result = solve()
    output = {"solution": result}
    print(json.dumps(output, ensure_ascii=False, indent=2))