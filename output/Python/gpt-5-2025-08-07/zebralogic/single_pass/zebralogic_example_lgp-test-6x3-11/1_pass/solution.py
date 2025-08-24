import json

def solve_puzzle():
    # Constants
    HOUSES = 6
    houses_idx = list(range(HOUSES))  # 0..5 correspond to houses 1..6

    Names = ['Bob', 'Peter', 'Eric', 'Alice', 'Arnold', 'Carol']
    HairColors = ['auburn', 'blonde', 'brown', 'black', 'red', 'gray']
    Heights = ['very tall', 'average', 'very short', 'tall', 'super tall', 'short']

    # State arrays indexed by house (0..5)
    names = [None] * HOUSES
    hairs = [None] * HOUSES
    heights = [None] * HOUSES

    # Helper functions
    def value_used(arr, val, except_index=None):
        for i, v in enumerate(arr):
            if i == except_index:
                continue
            if v == val:
                return True
        return False

    def try_assign(var_type, idx, value, trail):
        # Assign a single variable with checks and record for backtracking
        arr = names if var_type == 'name' else hairs if var_type == 'hair' else heights

        # Enforce per-variable fixed-position constraints immediately
        if var_type == 'name':
            # Alice is in the fourth house (index 3)
            if value == 'Alice' and idx != 3:
                return False
            if idx == 3 and value != 'Alice':
                return False
            # Uniqueness of names
            if value_used(names, value, except_index=idx):
                return False
        elif var_type == 'hair':
            # Gray hair is in the third house (index 2)
            if value == 'gray' and idx != 2:
                return False
            if idx == 2 and value != 'gray':
                return False
            # Black hair is not in the fourth house (index 3)
            if idx == 3 and value == 'black':
                return False
            # Distance of red from gray (one house between): with gray fixed at index 2,
            # red must be at index 0 or 4.
            if value == 'red' and idx not in (0, 4):
                return False
            # Uniqueness of hair colors
            if value_used(hairs, value, except_index=idx):
                return False
        elif var_type == 'height':
            # Very short is in the fifth house (index 4)
            if value == 'very short' and idx != 4:
                return False
            if idx == 4 and value != 'very short':
                return False
            # Tall is in the sixth house (index 5)
            if value == 'tall' and idx != 5:
                return False
            if idx == 5 and value != 'tall':
                return False
            # Uniqueness of heights
            if value_used(heights, value, except_index=idx):
                return False

        current = arr[idx]
        if current is None:
            arr[idx] = value
            trail.append((var_type, idx))
            return True
        else:
            return current == value

    def domain_name(i):
        if names[i] is not None:
            return {names[i]}
        used = {v for v in names if v is not None}
        dom = set(Names) - used
        # Alice in house 4 (index 3)
        if i == 3:
            return {'Alice'}
        else:
            dom.discard('Alice')

        # Hair-based constraints
        if hairs[i] == 'red':
            dom = {'Eric'} if 'Eric' in dom else set()
        elif hairs[i] is not None and hairs[i] != 'red':
            dom.discard('Eric')
        if hairs[i] == 'blonde':
            dom = {'Carol'} if 'Carol' in dom else set()
        elif hairs[i] is not None and hairs[i] != 'blonde':
            dom.discard('Carol')

        # Height-based constraints
        if heights[i] == 'short':
            dom = {'Arnold'} if 'Arnold' in dom else set()
        elif heights[i] is not None and heights[i] != 'short':
            dom.discard('Arnold')

        if heights[i] == 'very tall':
            dom = {'Carol'} if 'Carol' in dom else set()
        elif heights[i] is not None and heights[i] != 'very tall':
            dom.discard('Carol')

        # Adjacency: if left neighbor hair is blonde, this must be Bob
        if i > 0 and hairs[i - 1] == 'blonde':
            dom = {'Bob'} if 'Bob' in dom else set()

        return dom

    def domain_hair(i):
        if hairs[i] is not None:
            return {hairs[i]}
        used = {v for v in hairs if v is not None}
        dom = set(HairColors) - used

        # Fixed positions
        if i == 2:
            return {'gray'}
        dom.discard('gray')  # gray only allowed at index 2, already handled
        if i == 3:
            dom.discard('black')
        # Red must be two away from gray (index 2), i.e., at index 0 or 4
        if 'red' in dom and i not in (0, 4):
            dom.discard('red')

        # Name-based constraints
        if names[i] == 'Eric':
            dom = {'red'} if 'red' in dom else set()
        elif names[i] is not None and names[i] != 'Eric':
            dom.discard('red')

        if names[i] == 'Carol':
            dom = {'blonde'} if 'blonde' in dom else set()
        elif names[i] is not None and names[i] != 'Carol':
            dom.discard('blonde')

        # Height-based constraints
        if heights[i] == 'very tall':
            dom = {'blonde'} if 'blonde' in dom else set()
        elif heights[i] is not None and heights[i] != 'very tall':
            dom.discard('blonde')

        return dom

    def domain_height(i):
        if heights[i] is not None:
            return {heights[i]}
        used = {v for v in heights if v is not None}
        dom = set(Heights) - used

        # Fixed positions
        if i == 4:
            return {'very short'}
        if i == 5:
            return {'tall'}
        dom.discard('very short') if 'very short' in used or True else None  # ensure only at idx 4
        dom.discard('tall') if 'tall' in used or True else None  # ensure only at idx 5
        # Readd if at exact required positions (handled above), otherwise excluded

        # Name-based constraints
        if names[i] == 'Arnold':
            dom = {'short'} if 'short' in dom else set()
        elif names[i] is not None and names[i] != 'Arnold':
            dom.discard('short')

        if names[i] == 'Carol':
            dom = {'very tall'} if 'very tall' in dom else set()
        elif names[i] is not None and names[i] != 'Carol':
            dom.discard('very tall')

        # Hair-based constraints
        if hairs[i] == 'blonde':
            dom = {'very tall'} if 'very tall' in dom else set()
        elif hairs[i] is not None and hairs[i] != 'blonde':
            dom.discard('very tall')

        # Reintroduce average and super tall (they may have been removed by used set)
        # Actually used set has not removed them unless already used; so dom is correct.

        return dom

    def propagate(trail):
        changed = True
        while changed:
            changed = False
            # Apply equivalence constraints across all houses
            for i in houses_idx:
                # Name <-> Hair for Eric/Red
                if names[i] == 'Eric':
                    if not try_assign('hair', i, 'red', trail):
                        return False
                    changed = True
                if hairs[i] == 'red':
                    if not try_assign('name', i, 'Eric', trail):
                        return False
                    changed = True

                # Name/Hair/Height equivalence for Carol/Blonde/Very Tall
                if names[i] == 'Carol':
                    if not try_assign('hair', i, 'blonde', trail):
                        return False
                    if not try_assign('height', i, 'very tall', trail):
                        return False
                    changed = True
                if hairs[i] == 'blonde':
                    if not try_assign('name', i, 'Carol', trail):
                        return False
                    if not try_assign('height', i, 'very tall', trail):
                        return False
                    changed = True
                if heights[i] == 'very tall':
                    if not try_assign('name', i, 'Carol', trail):
                        return False
                    if not try_assign('hair', i, 'blonde', trail):
                        return False
                    changed = True

                # Arnold <-> short
                if names[i] == 'Arnold':
                    if not try_assign('height', i, 'short', trail):
                        return False
                    changed = True
                if heights[i] == 'short':
                    if not try_assign('name', i, 'Arnold', trail):
                        return False
                    changed = True

                # Adjacency blonde directly left of Bob
                # If hair[i] == 'blonde', then name[i+1] == 'Bob'
                if hairs[i] == 'blonde':
                    if i + 1 >= HOUSES:
                        return False
                    if not try_assign('name', i + 1, 'Bob', trail):
                        return False
                    changed = True
                # If name[i] == 'Bob', then hair[i-1] == 'blonde'
                if names[i] == 'Bob':
                    if i - 1 < 0:
                        return False
                    if not try_assign('hair', i - 1, 'blonde', trail):
                        return False
                    changed = True
        return True

    def consistency_check():
        # Fixed constraints
        if names[3] is not None and names[3] != 'Alice':
            return False
        if hairs[2] is not None and hairs[2] != 'gray':
            return False
        if heights[4] is not None and heights[4] != 'very short':
            return False
        if heights[5] is not None and heights[5] != 'tall':
            return False
        if hairs[3] == 'black':
            return False

        # Equivalence checks and contradictions
        for i in houses_idx:
            # Eric <-> red
            if names[i] == 'Eric' and hairs[i] is not None and hairs[i] != 'red':
                return False
            if hairs[i] == 'red' and names[i] is not None and names[i] != 'Eric':
                return False
            # Arnold <-> short
            if names[i] == 'Arnold' and heights[i] is not None and heights[i] != 'short':
                return False
            if heights[i] == 'short' and names[i] is not None and names[i] != 'Arnold':
                return False
            # Carol <-> blonde <-> very tall
            if names[i] == 'Carol':
                if hairs[i] is not None and hairs[i] != 'blonde':
                    return False
                if heights[i] is not None and heights[i] != 'very tall':
                    return False
            if hairs[i] == 'blonde':
                if names[i] is not None and names[i] != 'Carol':
                    return False
                if heights[i] is not None and heights[i] != 'very tall':
                    return False
            if heights[i] == 'very tall':
                if names[i] is not None and names[i] != 'Carol':
                    return False
                if hairs[i] is not None and hairs[i] != 'blonde':
                    return False

        # Adjacency: blonde is directly left of Bob
        def find_index(arr, val):
            for j, v in enumerate(arr):
                if v == val:
                    return j
            return None

        pos_bob = find_index(names, 'Bob')
        pos_blonde = find_index(hairs, 'blonde')

        if pos_bob is not None and pos_blonde is not None:
            if pos_bob != pos_blonde + 1:
                return False
        elif pos_bob is not None:
            if pos_bob == 0:
                return False
            # Ensure possibility that hair[pos_bob-1] can be blonde
            if hairs[pos_bob - 1] is not None and hairs[pos_bob - 1] != 'blonde':
                return False
            # Check domain feasibility
            if 'blonde' not in domain_hair(pos_bob - 1):
                return False
        elif pos_blonde is not None:
            if pos_blonde == HOUSES - 1:
                return False
            # Ensure names[pos_blonde+1] can be Bob
            if names[pos_blonde + 1] is not None and names[pos_blonde + 1] != 'Bob':
                return False
            if 'Bob' not in domain_name(pos_blonde + 1):
                return False

        # Gray/red spacing: with gray fixed at 3rd house (index 2), red must be at index 0 or 4
        pos_red = find_index(hairs, 'red')
        if pos_red is not None:
            if abs(pos_red - 2) != 2:
                return False
        else:
            # Ensure at least one possible place remains (0 or 4)
            possible = False
            for k in (0, 4):
                if 'red' in domain_hair(k):
                    possible = True
                    break
            if not possible:
                return False

        # Super tall to the right of average
        pos_super = find_index(heights, 'super tall')
        pos_avg = find_index(heights, 'average')
        if pos_super is not None and pos_avg is not None:
            if pos_super <= pos_avg:
                return False
        elif pos_super is not None and pos_avg is None:
            # Check if any possible position for average is left of super tall
            possible_left = False
            for i in range(pos_super):
                if 'average' in domain_height(i):
                    possible_left = True
                    break
            if not possible_left:
                return False
        elif pos_avg is not None and pos_super is None:
            # Check if any possible position for super tall is right of average
            possible_right = False
            for i in range(pos_avg + 1, HOUSES):
                if 'super tall' in domain_height(i):
                    possible_right = True
                    break
            if not possible_right:
                return False

        # Black hair is not in 4th house checked above; ensure no duplicate values across categories
        # Uniqueness checks (optional since domains prevent duplicates)
        if len([v for v in names if v is not None]) != len(set([v for v in names if v is not None])):
            return False
        if len([v for v in hairs if v is not None]) != len(set([v for v in hairs if v is not None])):
            return False
        if len([v for v in heights if v is not None]) != len(set([v for v in heights if v is not None])):
            return False

        return True

    def select_next_variable():
        candidates = []
        # Names
        for i in houses_idx:
            if names[i] is None:
                dn = domain_name(i)
                if len(dn) == 0:
                    return ('name', i, dn)
                candidates.append(('name', i, dn))
        # Hairs
        for i in houses_idx:
            if hairs[i] is None:
                dh = domain_hair(i)
                if len(dh) == 0:
                    return ('hair', i, dh)
                candidates.append(('hair', i, dh))
        # Heights
        for i in houses_idx:
            if heights[i] is None:
                dhg = domain_height(i)
                if len(dhg) == 0:
                    return ('height', i, dhg)
                candidates.append(('height', i, dhg))
        if not candidates:
            return None
        # Choose the variable with the smallest domain
        candidates.sort(key=lambda x: len(x[2]))
        return candidates[0]

    def backtrack():
        # If all assigned, check final consistency and return True
        if all(n is not None for n in names) and all(h is not None for h in hairs) and all(hg is not None for hg in heights):
            return consistency_check()
        # Choose variable
        choice = select_next_variable()
        if choice is None:
            return consistency_check()
        var_type, idx, domain_vals = choice
        if len(domain_vals) == 0:
            return False
        # Try each value
        for val in list(domain_vals):
            trail = []
            if not try_assign(var_type, idx, val, trail):
                # undo not needed as nothing changed
                continue
            if not propagate(trail):
                # Undo
                for vt, vi in reversed(trail):
                    arr = names if vt == 'name' else hairs if vt == 'hair' else heights
                    arr[vi] = None
                continue
            if consistency_check():
                if backtrack():
                    return True
            # Undo trail
            for vt, vi in reversed(trail):
                arr = names if vt == 'name' else hairs if vt == 'hair' else heights
                arr[vi] = None
        return False

    # Initialize fixed assignments
    init_trail = []
    assert try_assign('name', 3, 'Alice', init_trail)
    assert try_assign('height', 4, 'very short', init_trail)
    assert try_assign('height', 5, 'tall', init_trail)
    assert try_assign('hair', 2, 'gray', init_trail)
    assert propagate(init_trail)
    if not consistency_check():
        raise RuntimeError("Initial constraints inconsistent.")

    solved = backtrack()
    if not solved:
        raise RuntimeError("No solution found.")

    # Build JSON result
    header = ["House", "Name", "HairColor", "Height"]
    rows = []
    for i in range(HOUSES):
        rows.append([str(i + 1), names[i], hairs[i], heights[i]])

    return {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False, indent=2))