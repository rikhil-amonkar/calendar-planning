import itertools
import json

def solve():
    houses = list(range(6))  # 0..5 correspond to houses 1..6

    # Attributes
    Names = ['Peter', 'Bob', 'Carol', 'Eric', 'Alice', 'Arnold']
    Pets = ['bird', 'dog', 'cat', 'rabbit', 'fish', 'hamster']
    Styles = ['victorian', 'ranch', 'modern', 'mediterranean', 'colonial', 'craftsman']
    Months = ['mar', 'sept', 'may', 'feb', 'jan', 'april']

    # Helper to find index of a value in an assignment list
    def pos_of(value, arr):
        return arr.index(value)

    # Fixed placements from clues:
    # 5. Carol is in the third house.
    # 8. Eric is in the sixth house.
    # 18. The person in a Craftsman-style house is in the fourth house.
    # 11. The person in a Craftsman-style house is Arnold. => Arnold is in the fourth house.
    # 4. The person living in a colonial-style house is in the second house.
    # 14. Peter is the person living in a colonial-style house. => Peter is in the second house.
    fixed_names = [None]*6
    fixed_names[2] = 'Carol'
    fixed_names[5] = 'Eric'
    fixed_names[3] = 'Arnold'
    fixed_names[1] = 'Peter'
    remaining_names_positions = [i for i,v in enumerate(fixed_names) if v is None]  # [0,4]
    remaining_names = ['Bob','Alice']

    name_options = []
    for perm in itertools.permutations(remaining_names, len(remaining_names_positions)):
        candidate = fixed_names[:]
        for idx, val in zip(remaining_names_positions, perm):
            candidate[idx] = val
        name_options.append(candidate)

    # Birthdays:
    # 3. May is in the second house.
    # 17. Carol is March. (and Carol is third house) => house 3 is March.
    # 15. January is directly left of April.
    # 2. January is somewhere to the left of September.
    # Generate valid birthday assignments
    bday_options = []
    for pJan in range(5):  # Jan must have a spot for Apr on the right
        if pJan in (1,2):
            continue  # can't be house 2 (May) or 3 (Mar)
        pApr = pJan + 1
        if pApr in (1,2):
            continue
        # Build initial
        months_by_pos = [None]*6
        months_by_pos[1] = 'may'
        months_by_pos[2] = 'mar'
        months_by_pos[pJan] = 'jan'
        months_by_pos[pApr] = 'april'
        # Place Sept to the right of Jan (unused pos)
        for pSept in range(6):
            if pSept in (1,2,pJan,pApr):
                continue
            if pSept > pJan:
                candidate = months_by_pos[:]
                candidate[pSept] = 'sept'
                # Fill the last with Feb
                rem = [i for i,v in enumerate(candidate) if v is None]
                if len(rem) == 1:
                    candidate[rem[0]] = 'feb'
                    # Validate clue 17 (Carol is March) aligns with names later; for now store
                    bday_options.append(candidate)

    # Styles:
    # 4. Colonial in second house.
    # 18. Craftsman in fourth house.
    # 6. Mediterranean not in sixth house.
    # 12. Colonial is somewhere left of Modern.
    fixed_styles = [None]*6
    fixed_styles[1] = 'colonial'
    fixed_styles[3] = 'craftsman'
    remaining_style_positions = [i for i,v in enumerate(fixed_styles) if v is None]  # [0,2,4,5]
    remaining_styles = ['victorian', 'ranch', 'modern', 'mediterranean']

    style_options = []
    for perm in itertools.permutations(remaining_styles, len(remaining_style_positions)):
        candidate = fixed_styles[:]
        ok = True
        for idx, val in zip(remaining_style_positions, perm):
            candidate[idx] = val
        # 6. Mediterranean not in sixth house.
        if candidate[5] == 'mediterranean':
            ok = False
        # 12. Colonial (pos 1) is left of Modern
        if ok:
            if not (pos_of('colonial', candidate) < pos_of('modern', candidate)):
                ok = False
        if ok:
            style_options.append(candidate)

    # Pets:
    # 19. Dog is in the fourth house.
    fixed_pets = [None]*6
    fixed_pets[3] = 'dog'
    remaining_pet_positions = [i for i,v in enumerate(fixed_pets) if v is None]
    remaining_pets = [p for p in Pets if p != 'dog']

    solutions = []

    for names in name_options:
        # 17. Carol is March
        for bdays in bday_options:
            if names[pos_of('Carol', names)] != 'Carol':
                pass  # redundant
            if pos_of('mar', bdays) != pos_of('Carol', names):
                continue
            # 3. May is in second house (already enforced)
            if bdays[1] != 'may':
                continue
            # 2. Jan left of Sept (already enforced by construction)
            for styles in style_options:
                # 11. Craftsman is Arnold (already implied by fixed positions)
                if pos_of('craftsman', styles) != pos_of('Arnold', names):
                    continue
                # 14. Peter lives in colonial
                if pos_of('Peter', names) != pos_of('colonial', styles):
                    continue

                # Generate pets with constraints
                for perm in itertools.permutations(remaining_pets, len(remaining_pet_positions)):
                    pets = fixed_pets[:]
                    for idx, val in zip(remaining_pet_positions, perm):
                        pets[idx] = val

                    # 13. Fish not in second house.
                    if pets[1] == 'fish':
                        continue
                    # 1. Hamster to the right of March.
                    if pos_of('hamster', pets) <= pos_of('mar', bdays):
                        continue
                    # 7. Fish to the right of Bob.
                    if pos_of('fish', pets) <= pos_of('Bob', names):
                        continue
                    # 9. One house between Cat and Victorian.
                    if abs(pos_of('cat', pets) - pos_of('victorian', styles)) != 2:
                        continue
                    # 10. Two houses between Victorian and Hamster (distance 3).
                    if abs(pos_of('victorian', styles) - pos_of('hamster', pets)) != 3:
                        continue
                    # 16. One house between Bird and Modern (distance 2).
                    if abs(pos_of('bird', pets) - pos_of('modern', styles)) != 2:
                        continue
                    # 6. Mediterranean not in sixth house (already in styles)
                    if styles[5] == 'mediterranean':
                        continue
                    # 18. Craftsman in 4th (already)
                    if styles[3] != 'craftsman':
                        continue
                    # 19. Dog in 4th (already)
                    if pets[3] != 'dog':
                        continue

                    # All constraints satisfied; record solution
                    solutions.append((names, pets, styles, bdays))

    if not solutions:
        raise RuntimeError("No solution found")
    # Expect unique solution; take the first
    names, pets, styles, bdays = solutions[0]

    # Build JSON result
    header = ["House", "Name", "Pet", "HouseStyle", "Birthday"]
    rows = []
    for i in range(6):
        rows.append([str(i+1), names[i], pets[i], styles[i], bdays[i]])

    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    solution = solve()
    print(json.dumps(solution, ensure_ascii=False))