import json

def solve_puzzle():
    # Houses indexed 0..5 (representing 1..6)
    N = 6

    Names = ["Arnold", "Eric", "Bob", "Alice", "Carol", "Peter"]
    Mothers = ["Sarah", "Holly", "Janelle", "Aniya", "Penny", "Kailyn"]
    Pets = ["hamster", "dog", "bird", "cat", "fish", "rabbit"]

    names = [None] * N
    mothers = [None] * N
    pets = [None] * N

    used_names = set()
    used_mothers = set()
    used_pets = set()

    def positions_of(arr, val):
        return [i for i, v in enumerate(arr) if v == val]

    def check_constraints():
        # Rule 1: Bob is not in the second house (index 1)
        if names[1] == "Bob":
            return False

        # Equivalences and per-position constraints
        for i in range(N):
            # 7 and 10: Cat <-> Janelle <-> Arnold
            if pets[i] == "cat":
                if names[i] is not None and names[i] != "Arnold":
                    return False
                if mothers[i] is not None and mothers[i] != "Janelle":
                    return False
            if names[i] == "Arnold":
                if pets[i] is not None and pets[i] != "cat":
                    return False
                if mothers[i] is not None and mothers[i] != "Janelle":
                    return False
            if mothers[i] == "Janelle":
                if pets[i] is not None and pets[i] != "cat":
                    return False
                if names[i] is not None and names[i] != "Arnold":
                    return False

            # 5 and 11: Rabbit <-> Eric <-> Kailyn
            if pets[i] == "rabbit":
                if names[i] is not None and names[i] != "Eric":
                    return False
                if mothers[i] is not None and mothers[i] != "Kailyn":
                    return False
            if names[i] == "Eric":
                if pets[i] is not None and pets[i] != "rabbit":
                    return False
                if mothers[i] is not None and mothers[i] != "Kailyn":
                    return False
            if mothers[i] == "Kailyn":
                if pets[i] is not None and pets[i] != "rabbit":
                    return False
                if names[i] is not None and names[i] != "Eric":
                    return False

            # 9: Carol <-> Aniya
            if names[i] == "Carol":
                if mothers[i] is not None and mothers[i] != "Aniya":
                    return False
            if mothers[i] == "Aniya":
                if names[i] is not None and names[i] != "Carol":
                    return False

            # 12: Fish <-> Sarah
            if pets[i] == "fish":
                if mothers[i] is not None and mothers[i] != "Sarah":
                    return False
            if mothers[i] == "Sarah":
                if pets[i] is not None and pets[i] != "fish":
                    return False

        # Cross-house equivalence must align to same index if both sides assigned somewhere
        def enforce_same_house(attr1, val1, attr2, val2):
            arr1 = {"name": names, "mother": mothers, "pet": pets}[attr1]
            arr2 = {"name": names, "mother": mothers, "pet": pets}[attr2]
            p1 = positions_of(arr1, val1)
            p2 = positions_of(arr2, val2)
            if p1 and p2 and p1[0] != p2[0]:
                return False
            return True

        # Pairs to enforce
        same_pairs = [
            ("mother", "Aniya", "name", "Carol"),
            ("mother", "Sarah", "pet", "fish"),
            ("mother", "Kailyn", "pet", "rabbit"),
            ("mother", "Kailyn", "name", "Eric"),
            ("pet", "rabbit", "name", "Eric"),
            ("pet", "cat", "name", "Arnold"),
            ("pet", "cat", "mother", "Janelle"),
            ("mother", "Janelle", "name", "Arnold"),
        ]
        for a1, v1, a2, v2 in same_pairs:
            if not enforce_same_house(a1, v1, a2, v2):
                return False

        # 3: Cat is directly left of Holly
        pos_cat = positions_of(pets, "cat")
        pos_hol = positions_of(mothers, "Holly")
        if pos_cat:
            i = pos_cat[0]
            if i == N - 1:
                return False
            if mothers[i + 1] is not None and mothers[i + 1] != "Holly":
                return False
            if pos_hol and pos_hol[0] != i + 1:
                return False
        if pos_hol:
            j = pos_hol[0]
            if j == 0:
                return False
            if pets[j - 1] is not None and pets[j - 1] != "cat":
                return False
            if pos_cat and pos_cat[0] != j - 1:
                return False

        # 4: Hamster is directly left of Rabbit
        pos_ham = positions_of(pets, "hamster")
        pos_rab = positions_of(pets, "rabbit")
        if pos_ham:
            i = pos_ham[0]
            if i == N - 1:
                return False
            if pets[i + 1] is not None and pets[i + 1] != "rabbit":
                return False
            if pos_rab and pos_rab[0] != i + 1:
                return False
        if pos_rab:
            r = pos_rab[0]
            if r == 0:
                return False
            if pets[r - 1] is not None and pets[r - 1] != "hamster":
                return False
            if pos_ham and pos_ham[0] != r - 1:
                return False

        # 2: Two houses between Cat and Rabbit (difference of 3)
        if pos_cat and pos_rab:
            if abs(pos_cat[0] - pos_rab[0]) != 3:
                return False

        # 6: One house between Dog and Cat (difference of 2)
        pos_dog = positions_of(pets, "dog")
        if pos_dog and pos_cat:
            if abs(pos_dog[0] - pos_cat[0]) != 2:
                return False
        elif pos_dog and not pos_cat:
            d = pos_dog[0]
            candidates = [d - 2, d + 2]
            ok = False
            for c in candidates:
                if 0 <= c < N:
                    if pets[c] is None or pets[c] == "cat":
                        ok = True
            if not ok:
                return False
        elif pos_cat and not pos_dog:
            c = pos_cat[0]
            candidates = [c - 2, c + 2]
            ok = False
            for d in candidates:
                if 0 <= d < N:
                    if pets[d] is None or pets[d] == "dog":
                        ok = True
            if not ok:
                return False

        # 8: Alice is directly left of Carol
        pos_alice = positions_of(names, "Alice")
        pos_carol = positions_of(names, "Carol")
        if pos_alice:
            i = pos_alice[0]
            if i == N - 1:
                return False
            if names[i + 1] is not None and names[i + 1] != "Carol":
                return False
            if pos_carol and pos_carol[0] != i + 1:
                return False
        if pos_carol:
            j = pos_carol[0]
            if j == 0:
                return False
            if names[j - 1] is not None and names[j - 1] != "Alice":
                return False
            if pos_alice and pos_alice[0] != j - 1:
                return False

        return True

    def generate_triples_for_house(idx):
        triples = []
        # Allowed values considering used sets
        cand_names = [n for n in Names if n not in used_names and not (idx == 1 and n == "Bob")]
        cand_mothers = [m for m in Mothers if m not in used_mothers]
        cand_pets = [p for p in Pets if p not in used_pets]

        for n in cand_names:
            for m in cand_mothers:
                for p in cand_pets:
                    # Local consistency filters (equivalences and edges)
                    # Equivalences
                    if n == "Eric" and not (p == "rabbit" and m == "Kailyn"):
                        continue
                    if p == "rabbit" and not (n == "Eric" and m == "Kailyn"):
                        continue
                    if m == "Kailyn" and not (n == "Eric" and p == "rabbit"):
                        continue

                    if n == "Arnold" and not (p == "cat" and m == "Janelle"):
                        continue
                    if p == "cat" and not (n == "Arnold" and m == "Janelle"):
                        continue
                    if m == "Janelle" and not (n == "Arnold" and p == "cat"):
                        continue

                    if n == "Carol" and m != "Aniya":
                        continue
                    if m == "Aniya" and n != "Carol":
                        continue

                    if p == "fish" and m != "Sarah":
                        continue
                    if m == "Sarah" and p != "fish":
                        continue

                    # Edge feasibility for neighbor-required relations
                    if n == "Alice" and idx == N - 1:
                        continue
                    if n == "Carol" and idx == 0:
                        continue
                    if p == "cat" and idx == N - 1:
                        continue
                    if m == "Holly" and idx == 0:
                        continue
                    if p == "hamster" and idx == N - 1:
                        continue
                    if p == "rabbit" and idx == 0:
                        continue

                    # Check already assigned neighbors consistency
                    if n == "Alice":
                        right = idx + 1
                        if right < N and names[right] is not None and names[right] != "Carol":
                            continue
                    if n == "Carol":
                        left = idx - 1
                        if left >= 0 and names[left] is not None and names[left] != "Alice":
                            continue
                    if p == "cat":
                        right = idx + 1
                        if right < N and mothers[right] is not None and mothers[right] != "Holly":
                            continue
                    if m == "Holly":
                        left = idx - 1
                        if left >= 0 and pets[left] is not None and pets[left] != "cat":
                            continue
                    if p == "hamster":
                        right = idx + 1
                        if right < N and pets[right] is not None and pets[right] != "rabbit":
                            continue
                    if p == "rabbit":
                        left = idx - 1
                        if left >= 0 and pets[left] is not None and pets[left] != "hamster":
                            continue

                    # Dog-cat distance local viability
                    # If assigning dog here, ensure a cat can exist at idx-2 or idx+2 given current pets
                    if p == "dog":
                        candidates = []
                        for c in (idx - 2, idx + 2):
                            if 0 <= c < N:
                                candidates.append(c)
                        if not candidates:
                            continue
                        ok = False
                        for c in candidates:
                            if pets[c] is None or pets[c] == "cat":
                                ok = True
                        if not ok:
                            continue
                    if p == "cat":
                        # If an existing dog assigned elsewhere that is not 2 away, reject
                        dog_pos = positions_of(pets, "dog")
                        if dog_pos:
                            if abs(dog_pos[0] - idx) != 2:
                                continue
                        # Otherwise ensure there exists a place 2 away that could be dog
                        candidates = []
                        for d in (idx - 2, idx + 2):
                            if 0 <= d < N:
                                candidates.append(d)
                        if not candidates:
                            continue
                        ok = False
                        for d in candidates:
                            if pets[d] is None or pets[d] == "dog":
                                ok = True
                        if not ok:
                            continue

                    triples.append((n, m, p))
        return triples

    def choose_next_house():
        best_idx = None
        best_options = None
        best_len = None
        for idx in range(N):
            if names[idx] is None:
                options = generate_triples_for_house(idx)
                if best_len is None or len(options) < best_len:
                    best_len = len(options)
                    best_options = options
                    best_idx = idx
                if best_len == 0:
                    break
        return best_idx, best_options

    solution_found = False

    def backtrack():
        nonlocal solution_found
        if all(names[i] is not None for i in range(N)):
            # Full assignment, final constraint check
            if check_constraints():
                solution_found = True
                return True
            return False

        idx, options = choose_next_house()
        if options is None or len(options) == 0:
            return False

        for n, m, p in options:
            # Assign
            names[idx] = n
            mothers[idx] = m
            pets[idx] = p
            used_names.add(n)
            used_mothers.add(m)
            used_pets.add(p)

            if check_constraints():
                if backtrack():
                    return True

            # Undo
            used_names.remove(n)
            used_mothers.remove(m)
            used_pets.remove(p)
            names[idx] = None
            mothers[idx] = None
            pets[idx] = None

        return False

    backtrack()

    if not solution_found:
        raise RuntimeError("No solution found.")

    # Build JSON solution
    header = ["House", "Name", "Mother", "Pet"]
    rows = []
    for i in range(N):
        rows.append([str(i + 1), names[i], mothers[i], pets[i]])

    return {"solution": {"header": header, "rows": rows}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result))