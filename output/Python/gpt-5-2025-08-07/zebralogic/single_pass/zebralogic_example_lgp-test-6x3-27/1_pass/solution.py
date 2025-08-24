import json
from itertools import product

def solve_puzzle():
    houses = set(range(1, 7))

    names = ['Alice', 'Arnold', 'Eric', 'Peter', 'Bob', 'Carol']
    occupations = ['engineer', 'artist', 'doctor', 'teacher', 'nurse', 'lawyer']
    cars = ['chevrolet silverado', 'ford f150', 'honda civic', 'toyota camry', 'bmw 3 series', 'tesla model 3']

    # Variables represented as tuples: (category, value)
    name_vars = [('name', n) for n in names]
    occ_vars = [('occupation', o) for o in occupations]
    car_vars = [('car', c) for c in cars]
    all_vars = name_vars + occ_vars + car_vars

    # Helpful lookup for categories
    categories = {
        'name': names,
        'occupation': occupations,
        'car': cars
    }

    # Equality constraints (must be same house)
    equality_pairs = [
        (('occupation', 'doctor'), ('name', 'Eric')),
        (('occupation', 'engineer'), ('name', 'Bob')),
        (('occupation', 'artist'), ('name', 'Arnold')),
        (('car', 'toyota camry'), ('occupation', 'nurse')),
    ]

    # Adjacent constraints (difference exactly 1)
    adjacent_pairs = [
        (('car', 'honda civic'), ('name', 'Peter')),
    ]

    # One-between constraints (difference exactly 2)
    one_between_pairs = [
        (('name', 'Peter'), ('occupation', 'lawyer')),
        (('car', 'tesla model 3'), ('name', 'Bob')),
    ]

    # Specific left/right constraints
    # Nurse directly left of Artist: nurse = artist - 1
    nurse_var = ('occupation', 'nurse')
    artist_var = ('occupation', 'artist')

    # Teacher somewhere to the left of Nurse: teacher < nurse
    teacher_var = ('occupation', 'teacher')

    # Carol somewhere to the right of Eric: Carol > Eric
    carol_var = ('name', 'Carol')
    eric_var = ('name', 'Eric')

    # Unary constraints for quick checks
    def unary_constraints(var, base_domain):
        cat, val = var
        domain = set(base_domain)

        # All unary constraints
        if var == ('car', 'ford f150'):
            domain &= {5}
        if var == ('car', 'chevrolet silverado'):
            domain -= {2}
        if var == ('occupation', 'lawyer'):
            domain -= {5}
        if var == ('name', 'Carol'):
            # Carol is not in the sixth house, and must be to the right of Eric -> cannot be 1 either
            domain -= {6, 1}
        # From nurse directly left of artist and teacher left of nurse:
        # Nurse cannot be 1 (teacher must be left of nurse) and cannot be 6 (needs artist on right)
        if var == ('occupation', 'nurse'):
            domain &= {2, 3, 4, 5}
        # Artist cannot be 1 or 2 (since nurse must be directly left and nurse != 1 due to teacher)
        if var == ('occupation', 'artist'):
            domain &= {3, 4, 5, 6}
        # Teacher cannot be 6 (must be left of nurse)
        if var == ('occupation', 'teacher'):
            domain &= {1, 2, 3, 4, 5}
        # Arnold is the artist -> Arnold shares domain nature with artist
        if var == ('name', 'Arnold'):
            domain &= {3, 4, 5, 6}
        # Toyota Camry is the nurse's car -> same domain nature as nurse
        if var == ('car', 'toyota camry'):
            domain &= {2, 3, 4, 5}

        return domain

    def assigned_in_category(assignment, category):
        return {assignment[v] for v in assignment if v[0] == category}

    # Compute domain for a variable given current partial assignment
    def compute_domain(var, assignment):
        base = set(houses)
        cat, val = var

        # Enforce all-different within category
        base -= assigned_in_category(assignment, cat)

        # Apply unary constraints
        base = unary_constraints(var, base)

        # Apply binary constraints with currently assigned partners
        # Equalities
        for a, b in equality_pairs:
            if var == a and b in assignment:
                base &= {assignment[b]}
            elif var == b and a in assignment:
                base &= {assignment[a]}

        # Nurse directly left of Artist
        if var == nurse_var and artist_var in assignment:
            base &= {assignment[artist_var] - 1}
        if var == artist_var and nurse_var in assignment:
            base &= {assignment[nurse_var] + 1}

        # Teacher left of Nurse
        if var == teacher_var and nurse_var in assignment:
            base = {h for h in base if h < assignment[nurse_var]}
        if var == nurse_var and teacher_var in assignment:
            base = {h for h in base if h > assignment[teacher_var]}

        # Adjacent pairs
        for a, b in adjacent_pairs:
            if var == a and b in assignment:
                p = assignment[b]
                base &= {pos for pos in (p - 1, p + 1) if 1 <= pos <= 6}
            elif var == b and a in assignment:
                p = assignment[a]
                base &= {pos for pos in (p - 1, p + 1) if 1 <= pos <= 6}

        # One-between pairs (distance == 2)
        for a, b in one_between_pairs:
            if var == a and b in assignment:
                p = assignment[b]
                base &= {pos for pos in (p - 2, p + 2) if 1 <= pos <= 6}
            elif var == b and a in assignment:
                p = assignment[a]
                base &= {pos for pos in (p - 2, p + 2) if 1 <= pos <= 6}

        # Right-of constraint Carol > Eric
        if var == carol_var and eric_var in assignment:
            e = assignment[eric_var]
            base = {h for h in base if h > e}
        if var == eric_var and carol_var in assignment:
            c = assignment[carol_var]
            base = {h for h in base if h < c}

        return base

    # Check overall consistency for a partial assignment
    def constraints_ok(assignment):
        # Category all-different
        for cat in ['name', 'occupation', 'car']:
            seen = {}
            for v in assignment:
                if v[0] == cat:
                    pos = assignment[v]
                    if pos in seen:
                        return False
                    seen[pos] = True

        # Unary checks on assigned
        for v in assignment:
            pos = assignment[v]
            # ford f150 is in 5
            if v == ('car', 'ford f150') and pos != 5:
                return False
            # chevrolet silverado not in 2
            if v == ('car', 'chevrolet silverado') and pos == 2:
                return False
            # lawyer not in 5
            if v == ('occupation', 'lawyer') and pos == 5:
                return False
            # Carol not in 6 and not in 1 (since must be right of Eric)
            if v == ('name', 'Carol') and pos in (1, 6):
                return False
            # nurse domain basic
            if v == ('occupation', 'nurse') and pos not in {2, 3, 4, 5}:
                return False
            # artist domain basic
            if v == ('occupation', 'artist') and pos not in {3, 4, 5, 6}:
                return False
            # teacher domain basic
            if v == ('occupation', 'teacher') and pos not in {1, 2, 3, 4, 5}:
                return False
            # Arnold domain basic
            if v == ('name', 'Arnold') and pos not in {3, 4, 5, 6}:
                return False
            # Camry domain basic
            if v == ('car', 'toyota camry') and pos not in {2, 3, 4, 5}:
                return False

        # Equalities
        for a, b in equality_pairs:
            if a in assignment and b in assignment:
                if assignment[a] != assignment[b]:
                    return False

        # Nurse directly left of artist
        if nurse_var in assignment and artist_var in assignment:
            if assignment[nurse_var] + 1 != assignment[artist_var]:
                return False

        # Teacher left of nurse
        if teacher_var in assignment and nurse_var in assignment:
            if not (assignment[teacher_var] < assignment[nurse_var]):
                return False

        # Adjacent pairs
        for a, b in adjacent_pairs:
            if a in assignment and b in assignment:
                if abs(assignment[a] - assignment[b]) != 1:
                    return False

        # One-between pairs
        for a, b in one_between_pairs:
            if a in assignment and b in assignment:
                if abs(assignment[a] - assignment[b]) != 2:
                    return False

        # Carol right of Eric
        if carol_var in assignment and eric_var in assignment:
            if not (assignment[carol_var] > assignment[eric_var]):
                return False

        return True

    def forward_check(assignment):
        # Ensure every unassigned variable has at least one possible value
        for var in all_vars:
            if var not in assignment:
                dom = compute_domain(var, assignment)
                if not dom:
                    return False
        return True

    # MRV heuristic to pick next variable
    def select_unassigned_var(assignment):
        candidates = []
        for var in all_vars:
            if var not in assignment:
                dom = compute_domain(var, assignment)
                candidates.append((len(dom), var, sorted(dom)))
        # Sort by domain size, then by category for stability
        candidates.sort(key=lambda x: (x[0], x[1][0], x[1][1]))
        if not candidates:
            return None, []
        return candidates[0][1], candidates[0][2]

    def backtrack(assignment):
        if len(assignment) == len(all_vars):
            if constraints_ok(assignment):
                return assignment
            return None

        var, domain_vals = select_unassigned_var(assignment)
        if var is None:
            return None
        # Try each value in domain
        for val in domain_vals:
            assignment[var] = val
            if constraints_ok(assignment) and forward_check(assignment):
                result = backtrack(assignment)
                if result is not None:
                    return result
            del assignment[var]
        return None

    solution_assignment = backtrack({})

    if solution_assignment is None:
        raise ValueError("No solution found")

    # Build output mapping: for each house, get Name, Occupation, CarModel
    house_to = {h: {'Name': None, 'Occupation': None, 'CarModel': None} for h in range(1, 7)}

    for (cat, val), pos in solution_assignment.items():
        if cat == 'name':
            house_to[pos]['Name'] = val
        elif cat == 'occupation':
            house_to[pos]['Occupation'] = val
        elif cat == 'car':
            house_to[pos]['CarModel'] = val

    # Prepare JSON output
    rows = []
    for h in range(1, 7):
        rows.append([str(h), house_to[h]['Name'], house_to[h]['Occupation'], house_to[h]['CarModel']])

    output = {
        "solution": {
            "header": ["House", "Name", "Occupation", "CarModel"],
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False, indent=2))