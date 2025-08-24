import itertools
import json

def solve():
    houses = [0, 1, 2]  # indices for houses 1..3
    categories = {
        "Name": ["Arnold", "Peter", "Eric"],
        "Animal": ["bird", "horse", "cat"],
        "Birthday": ["jan", "sept", "april"],
        "Hobby": ["photography", "cooking", "gardening"],
        "Drink": ["milk", "water", "tea"],
        "HairColor": ["black", "brown", "blonde"],
    }

    # Order categories for efficient pruning
    order = ["Animal", "HairColor", "Hobby", "Drink", "Birthday", "Name"]

    # Precompute domains with simple clue-based filtering
    def domain_for(category):
        items = categories[category]
        perms = list(itertools.permutations(items))
        # Apply simple domain pruning based on direct clues
        if category == "Animal":
            perms = [p for p in perms if p[1] == "cat"]  # Clue 4
        if category == "Birthday":
            perms = [p for p in perms if p[2] == "april"]  # Clue 2
        if category == "Name":
            perms = [p for p in perms if p[0] != "Eric"]  # Clue 3
        return [list(p) for p in perms]

    domains = {cat: domain_for(cat) for cat in order}

    def pos_of(assignment, cat, value):
        if cat not in assignment:
            return None
        try:
            return assignment[cat].index(value)
        except ValueError:
            return None

    def check_biconditional(assignment, catA, valA, catB, valB):
        # For every house i, (catA==valA) iff (catB==valB)
        for i in houses:
            a_known = catA in assignment
            b_known = catB in assignment
            if a_known:
                a_val = assignment[catA][i]
                if a_val == valA and b_known and assignment[catB][i] != valB:
                    return False
                if a_val != valA and b_known and assignment[catB][i] == valB:
                    return False
            if b_known:
                b_val = assignment[catB][i]
                if b_val == valB and a_known and assignment[catA][i] != valA:
                    return False
                if b_val != valB and a_known and assignment[catA][i] == valA:
                    return False
        return True

    def check_left_of(assignment, catA, valA, catB, valB):
        # Enforce position(catA=valA) < position(catB=valB)
        posA = pos_of(assignment, catA, valA)
        posB = pos_of(assignment, catB, valB)
        if posA is not None and posB is not None:
            return posA < posB
        # Partial checks for pruning
        if posA is not None and posA == 2:
            return False  # cannot be left of anyone
        if posB is not None and posB == 0:
            return False  # nothing left of house 1
        return True

    def check_directly_left_of(assignment, catA, valA, catB, valB):
        # Enforce position(catA=valA) + 1 == position(catB=valB)
        posA = pos_of(assignment, catA, valA)
        posB = pos_of(assignment, catB, valB)
        if posA is not None and posB is not None:
            return posA + 1 == posB
        # Partial pruning
        if posA is not None and posA == 2:
            return False  # cannot be directly left if at rightmost
        if posB is not None and posB == 0:
            return False  # cannot have someone directly left of first house
        return True

    def check_constraints(assignment):
        # Clue 2: April is in the third house
        if "Birthday" in assignment and assignment["Birthday"][2] != "april":
            return False

        # Clue 3: Eric is not in the first house
        if "Name" in assignment and assignment["Name"][0] == "Eric":
            return False

        # Clue 4: The cat lover is in the second house
        if "Animal" in assignment and assignment["Animal"][1] != "cat":
            return False

        # Clue 1: Brown hair <-> Cooking
        if not check_biconditional(assignment, "HairColor", "brown", "Hobby", "cooking"):
            return False

        # Clue 6: Gardening <-> Milk
        if not check_biconditional(assignment, "Hobby", "gardening", "Drink", "milk"):
            return False

        # Clue 7: Cat <-> Brown hair
        if not check_biconditional(assignment, "Animal", "cat", "HairColor", "brown"):
            return False

        # Clue 8: Arnold <-> Bird
        if not check_biconditional(assignment, "Name", "Arnold", "Animal", "bird"):
            return False

        # Clue 9: Water <-> Photography
        if not check_biconditional(assignment, "Drink", "water", "Hobby", "photography"):
            return False

        # Clue 5: Blonde is left of Milk
        if not check_left_of(assignment, "HairColor", "blonde", "Drink", "milk"):
            return False
        # Extra early pruning for clue 5
        if "HairColor" in assignment and assignment["HairColor"][2] == "blonde":
            return False
        if "Drink" in assignment and assignment["Drink"][0] == "milk":
            return False

        # Clue 10: September is directly left of Arnold
        if not check_directly_left_of(assignment, "Birthday", "sept", "Name", "Arnold"):
            return False
        # Extra pruning for clue 10
        if "Birthday" in assignment and assignment["Birthday"][2] == "sept":
            return False
        if "Name" in assignment and assignment["Name"][0] == "Arnold":
            return False

        return True

    solution = None

    def backtrack(idx, assignment):
        nonlocal solution
        if solution is not None:
            return
        if idx == len(order):
            if check_constraints(assignment):
                solution = {k: v[:] for k, v in assignment.items()}
            return
        cat = order[idx]
        for perm in domains[cat]:
            assignment[cat] = perm
            if check_constraints(assignment):
                backtrack(idx + 1, assignment)
            if solution is not None:
                return
            del assignment[cat]

    backtrack(0, {})

    if solution is None:
        raise RuntimeError("No solution found")

    rows = []
    for i in range(3):
        rows.append([
            str(i + 1),
            solution["Name"][i],
            solution["Animal"][i],
            solution["Birthday"][i],
            solution["Hobby"][i],
            solution["Drink"][i],
            solution["HairColor"][i],
        ])

    output = {
        "solution": {
            "header": ["House", "Name", "Animal", "Birthday", "Hobby", "Drink", "HairColor"],
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve()
    print(json.dumps(result, ensure_ascii=False, indent=2))