import json
from itertools import permutations

def solve():
    houses = [1, 2, 3, 4, 5, 6]

    # Constants
    NAMES = ["Arnold", "Peter", "Bob", "Eric", "Carol", "Alice"]
    ANIMALS = ["horse", "rabbit", "fish", "cat", "bird", "dog"]
    OCCUPATIONS = ["engineer", "nurse", "lawyer", "teacher", "artist", "doctor"]
    SPORTS = ["basketball", "volleyball", "soccer", "tennis", "baseball", "swimming"]
    HEIGHTS = ["average", "tall", "short", "very short", "very tall", "super tall"]

    for tennis_pos in [3, 4]:
        sport = {i: None for i in houses}
        # Clue 18: Baseball in first house
        sport[1] = "baseball"
        # Clues 10 and 15: Tennis (teacher) is directly left of Soccer
        if tennis_pos + 1 > 6:
            continue
        sport[tennis_pos] = "tennis"
        soccer_pos = tennis_pos + 1
        sport[soccer_pos] = "soccer"

        # Remaining sports to place
        remaining_sports_houses = [i for i in houses if sport[i] is None]
        remaining_sports = ["basketball", "volleyball", "swimming"]

        for sp_perm in permutations(remaining_sports):
            sport2 = sport.copy()
            ok = True
            for i, s in zip(remaining_sports_houses, sp_perm):
                # Clue 20: House 5 is super tall, so cannot have volleyball (tall) or swimming (average)
                if i == 5 and s in ("volleyball", "swimming"):
                    ok = False
                    break
                sport2[i] = s
            if not ok:
                continue

            # Heights
            height = {i: None for i in houses}
            # Clue 20: Super tall in fifth house
            height[5] = "super tall"
            # Clue 8: Tall = Volleyball
            vol_pos = [i for i in houses if sport2[i] == "volleyball"]
            if len(vol_pos) != 1:
                continue
            VP = vol_pos[0]
            if VP == 5:
                continue
            height[VP] = "tall"
            # Clue 11: Average = Swimming
            swim_pos = [i for i in houses if sport2[i] == "swimming"]
            if len(swim_pos) != 1:
                continue
            SP = swim_pos[0]
            if SP == 5:
                continue
            height[SP] = "average"

            # Assign remaining heights with constraints:
            # - 'short', 'very short', 'very tall' go to remaining houses
            remaining_height_houses = [i for i in houses if height[i] is None]
            for ht_perm in permutations(["short", "very short", "very tall"], 3):
                ht2 = height.copy()
                for i, hv in zip(remaining_height_houses, ht_perm):
                    ht2[i] = hv

                # Clue 4: Tall is left of very short
                vshort_pos = [i for i in houses if ht2[i] == "very short"][0]
                if not (VP < vshort_pos):
                    continue
                # Clue 2: Average is left of short
                short_pos = [i for i in houses if ht2[i] == "short"][0]
                if not (SP < short_pos):
                    continue

                # Occupations
                occupation = {i: None for i in houses}
                # Clue 12 + 18: Engineer is directly right of baseball -> engineer at 2
                occupation[2] = "engineer"
                # Clue 9: Lawyer in fifth house
                occupation[5] = "lawyer"
                # Clues 6 + 10 + 15: Teacher at tennis position
                occupation[tennis_pos] = "teacher"

                occ_remaining_houses = [i for i in houses if occupation[i] is None]
                for occ_perm in permutations(["nurse", "artist", "doctor"], 3):
                    occ2 = occupation.copy()
                    for i, o in zip(occ_remaining_houses, occ_perm):
                        occ2[i] = o

                    # Animals
                    animal = {i: None for i in houses}
                    # Clue 1: Engineer is the dog owner
                    animal[2] = "dog"
                    # Clue 6: Horse = Teacher -> at tennis_pos
                    animal[tennis_pos] = "horse"
                    # Clue 7 + 17: Carol loves soccer and fish -> at soccer_pos
                    animal[soccer_pos] = "fish"

                    # Clue 3 + 11 + 16: Average (swimming) is directly left of rabbit owner (Alice)
                    if not (SP < 6):
                        continue
                    rabbit_pos = SP + 1
                    if animal[rabbit_pos] is not None:
                        # Rabbit conflicts with dog/horse/fish already set
                        continue
                    animal[rabbit_pos] = "rabbit"

                    # Remaining animals are cat and bird
                    remaining_animal_houses = [i for i in houses if animal[i] is None]
                    if len(remaining_animal_houses) != 2:
                        continue

                    for order in [(remaining_animal_houses[0], remaining_animal_houses[1]),
                                  (remaining_animal_houses[1], remaining_animal_houses[0])]:
                        cat_pos, bird_pos = order
                        # Clue 19: Cat lover is somewhere to the right of very short
                        if not (cat_pos > vshort_pos):
                            continue
                        an2 = animal.copy()
                        an2[cat_pos] = "cat"
                        an2[bird_pos] = "bird"

                        # Names
                        name = {i: None for i in houses}
                        # Clue 7 + 17: Carol at soccer_pos
                        name[soccer_pos] = "Carol"
                        # Clue 16: Alice at rabbit_pos
                        name[rabbit_pos] = "Alice"
                        # Clue 5: Arnold is the cat lover
                        name[cat_pos] = "Arnold"
                        # Clue 13: Peter is a nurse
                        nurse_pos = [i for i in houses if occ2[i] == "nurse"][0]
                        # If nurse_pos already taken by another name, skip
                        if name[nurse_pos] is not None and name[nurse_pos] != "Peter":
                            continue
                        name[nurse_pos] = "Peter"

                        # Remaining names: Bob and Eric
                        remaining_name_houses = [i for i in houses if name[i] is None]
                        remaining_names = ["Bob", "Eric"]
                        artist_pos = [i for i in houses if occ2[i] == "artist"][0]

                        for nm_perm in permutations(remaining_names):
                            nm2 = name.copy()
                            for i, nm in zip(remaining_name_houses, nm_perm):
                                nm2[i] = nm
                            # Clue 14: Bob is somewhere to the right of the artist
                            bob_pos = [i for i in houses if nm2[i] == "Bob"][0]
                            if not (bob_pos > artist_pos):
                                continue

                            # All constraints satisfied, build the solution
                            rows = []
                            for i in houses:
                                rows.append([
                                    str(i),
                                    nm2[i],
                                    an2[i],
                                    occ2[i],
                                    sport2[i],
                                    ht2[i]
                                ])
                            return rows
    return None

def main():
    rows = solve()
    if rows is None:
        raise RuntimeError("No solution found")
    solution = {
        "solution": {
            "header": ["House", "Name", "Animal", "Occupation", "FavoriteSport", "Height"],
            "rows": rows
        }
    }
    print(json.dumps(solution, ensure_ascii=False))

if __name__ == "__main__":
    main()