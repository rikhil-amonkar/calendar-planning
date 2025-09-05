import json
from collections import deque, defaultdict
import copy

def solve_puzzle():
    houses = list(range(6))  # 0..5 represent houses 1..6

    categories = {
        'Name': ['Arnold', 'Carol', 'Eric', 'Bob', 'Alice', 'Peter'],
        'Birthday': ['feb', 'mar', 'sept', 'jan', 'may', 'april'],
        'Food': ['stew', 'soup', 'grilled cheese', 'stir fry', 'spaghetti', 'pizza'],
        'Height': ['very short', 'average', 'super tall', 'short', 'very tall', 'tall'],
        'CarModel': ['chevrolet silverado', 'ford f150', 'bmw 3 series', 'tesla model 3', 'toyota camry', 'honda civic'],
    }

    # Variable is represented as a tuple (Category, Value)
    def var(cat, val):
        return (cat, val)

    # Initialize domains: every variable can be any house initially
    domains = {}
    for cat, vals in categories.items():
        for v in vals:
            domains[var(cat, v)] = set(houses)

    # Helper to add unary constraints (domain restrictions)
    def set_eq(variable, house_idx):
        domains[variable] = {house_idx}

    def set_neq(variable, house_idx):
        domains[variable].discard(house_idx)

    # Constraint relations
    def rel_eq(x, y):  # x == y
        return x == y

    def rel_neq(x, y):  # x != y
        return x != y

    def rel_lt(x, y):  # x < y
        return x < y

    def rel_offset_k(k):
        # returns function f(x,y): x + k == y
        return lambda x, y: (x + k) == y

    def rel_absdist_k(k):
        return lambda x, y: abs(x - y) == k

    # AC-3 setup
    arcs = []  # list of (X, Y, test)
    neighbors_out = defaultdict(list)  # X -> list of (Y, test)
    neighbors_in = defaultdict(list)   # Y -> list of (X, test)

    def add_arc(X, Y, test):
        arcs.append((X, Y, test))
        neighbors_out[X].append((Y, test))
        neighbors_in[Y].append((X, test))

    def add_binary_constraint(X, Y, test):
        # add (X,Y,test) and (Y,X,test_rev)
        add_arc(X, Y, test)
        def test_rev(a, b):
            return test(b, a)
        add_arc(Y, X, test_rev)

    # All-different within each category
    for cat, vals in categories.items():
        for i in range(len(vals)):
            for j in range(i + 1, len(vals)):
                X = var(cat, vals[i])
                Y = var(cat, vals[j])
                add_binary_constraint(X, Y, rel_neq)

    # Apply unary constraints from clues
    # 2. Ford F-150 in 5th house (index 4)
    set_eq(var('CarModel', 'ford f150'), 4)
    # 6. BMW 3 Series not in 3rd house (index 2)
    set_neq(var('CarModel', 'bmw 3 series'), 2)
    # 14. Stew not in 3rd house (index 2)
    set_neq(var('Food', 'stew'), 2)
    # 19. Very short is in the fourth house (index 3)
    set_eq(var('Height', 'very short'), 3)

    # Binary constraints from clues
    # 1. Honda Civic == short
    add_binary_constraint(var('CarModel', 'honda civic'), var('Height', 'short'), rel_eq)
    # 3. stir fry < Eric
    add_binary_constraint(var('Food', 'stir fry'), var('Name', 'Eric'), rel_lt)
    # 4. May < Carol
    add_binary_constraint(var('Birthday', 'may'), var('Name', 'Carol'), rel_lt)
    # 5. very short < April
    add_binary_constraint(var('Height', 'very short'), var('Birthday', 'april'), rel_lt)
    # 7. |stir fry - pizza| == 3
    add_binary_constraint(var('Food', 'stir fry'), var('Food', 'pizza'), rel_absdist_k(3))
    # 8. soup is directly left of Eric: soup +1 = Eric
    add_binary_constraint(var('Food', 'soup'), var('Name', 'Eric'), rel_offset_k(1))
    # 9. spaghetti and May are next to each other: |spaghetti - may| == 1
    add_binary_constraint(var('Food', 'spaghetti'), var('Birthday', 'may'), rel_absdist_k(1))
    # 10. Alice is directly left of BMW 3 Series: Alice +1 = BMW
    add_binary_constraint(var('Name', 'Alice'), var('CarModel', 'bmw 3 series'), rel_offset_k(1))
    # 11. Tesla Model 3 < tall
    add_binary_constraint(var('CarModel', 'tesla model 3'), var('Height', 'tall'), rel_lt)
    # 12. very tall == Toyota Camry
    add_binary_constraint(var('Height', 'very tall'), var('CarModel', 'toyota camry'), rel_eq)
    # 13. Peter is directly left of pizza: Peter +1 = pizza
    add_binary_constraint(var('Name', 'Peter'), var('Food', 'pizza'), rel_offset_k(1))
    # 15. |September - very short| == 2
    add_binary_constraint(var('Birthday', 'sept'), var('Height', 'very short'), rel_absdist_k(2))
    # 16. |March - super tall| == 2
    add_binary_constraint(var('Birthday', 'mar'), var('Height', 'super tall'), rel_absdist_k(2))
    # 17. tall == Bob
    add_binary_constraint(var('Height', 'tall'), var('Name', 'Bob'), rel_eq)
    # 18. May > Alice (Alice somewhere to the left of May): equivalently Alice < May
    add_binary_constraint(var('Name', 'Alice'), var('Birthday', 'may'), rel_lt)
    # 20. March == short
    add_binary_constraint(var('Birthday', 'mar'), var('Height', 'short'), rel_eq)
    # 21. Carol == Tesla Model 3
    add_binary_constraint(var('Name', 'Carol'), var('CarModel', 'tesla model 3'), rel_eq)
    # 22. Eric == January
    add_binary_constraint(var('Name', 'Eric'), var('Birthday', 'jan'), rel_eq)

    # AC-3 algorithm
    def ac3(domains):
        queue = deque(arcs)
        while queue:
            X, Y, test = queue.popleft()
            if revise(domains, X, Y, test):
                if not domains[X]:
                    return False
                # For all Z neighbors of X (inbound arcs), add (Z, X) to queue except the one from Y
                for Z, test_zx in neighbors_in[X]:
                    if Z != Y:
                        queue.append((Z, X, test_zx))
        return True

    def revise(domains, X, Y, test):
        revised = False
        domX = domains[X]
        domY = domains[Y]
        to_remove = set()
        for x in domX:
            # Check if there exists y in domY such that test(x,y) is True
            if not any(test(x, y) for y in domY):
                to_remove.add(x)
        if to_remove:
            domX.difference_update(to_remove)
            revised = True
        return revised

    # Backtracking search with AC-3 propagation
    def is_solved(domains):
        return all(len(dom) == 1 for dom in domains.values())

    def select_unassigned_variable(domains):
        # MRV heuristic: pick var with smallest domain > 1
        unassigned = [(len(dom), v) for v, dom in domains.items() if len(dom) > 1]
        if not unassigned:
            return None
        unassigned.sort()
        return unassigned[0][1]

    def backtrack(domains):
        if not ac3(domains):
            return None
        if is_solved(domains):
            return domains
        var_choice = select_unassigned_variable(domains)
        if var_choice is None:
            return None
        for value in sorted(domains[var_choice]):
            new_domains = copy.deepcopy(domains)
            new_domains[var_choice] = {value}
            result = backtrack(new_domains)
            if result is not None:
                return result
        return None

    solution_domains = backtrack(copy.deepcopy(domains))
    if solution_domains is None:
        raise ValueError("No solution found")

    # Build output mapping per house
    # For each category, build value -> house index
    pos_by_cat = {}
    for cat, vals in categories.items():
        mapping = {}
        for v in vals:
            d = solution_domains[var(cat, v)]
            assert len(d) == 1
            mapping[v] = next(iter(d))
        pos_by_cat[cat] = mapping

    # Build reverse mapping house -> attribute values
    result_rows = []
    header = ["House", "Name", "Birthday", "Food", "Height", "CarModel"]
    for h in range(6):
        # Find the value in each category at house h
        name_at_h = next(name for name, pos in pos_by_cat['Name'].items() if pos == h)
        bday_at_h = next(b for b, pos in pos_by_cat['Birthday'].items() if pos == h)
        food_at_h = next(f for f, pos in pos_by_cat['Food'].items() if pos == h)
        height_at_h = next(ht for ht, pos in pos_by_cat['Height'].items() if pos == h)
        car_at_h = next(c for c, pos in pos_by_cat['CarModel'].items() if pos == h)
        row = [str(h + 1), name_at_h, bday_at_h, food_at_h, height_at_h, car_at_h]
        result_rows.append(row)

    output = {
        "solution": {
            "header": header,
            "rows": result_rows
        }
    }
    return output

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))