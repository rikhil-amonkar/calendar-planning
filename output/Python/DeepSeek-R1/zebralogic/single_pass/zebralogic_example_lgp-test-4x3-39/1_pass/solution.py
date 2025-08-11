import itertools
import json

def satisfies(candidate):
    # Constraint 1: Soccer not in second house (index1)
    for i, house in enumerate(candidate):
        if house[2] == 'soccer' and i == 1:
            return False

    # Constraint 2: Eric has blonde hair
    for house in candidate:
        if house[0] == 'Eric':
            if house[1] != 'blonde':
                return False
            break

    # Constraint 3: Blonde hair right of basketball
    idx_blonde = None
    idx_basketball = None
    for i, house in enumerate(candidate):
        if house[1] == 'blonde':
            idx_blonde = i
        if house[2] == 'basketball':
            idx_basketball = i
    if idx_blonde is None or idx_basketball is None:
        return False
    if idx_blonde <= idx_basketball:
        return False

    # Constraint 4: Black hair implies tennis
    for house in candidate:
        if house[1] == 'black':
            if house[2] != 'tennis':
                return False
            break

    # Constraint 5: Arnold left of red hair
    idx_arnold = None
    idx_red = None
    for i, house in enumerate(candidate):
        if house[0] == 'Arnold':
            idx_arnold = i
        if house[1] == 'red':
            idx_red = i
    if idx_arnold is None or idx_red is None:
        return False
    if idx_arnold >= idx_red:
        return False

    # Constraint 6: Alice loves swimming
    for house in candidate:
        if house[0] == 'Alice':
            if house[2] != 'swimming':
                return False
            break

    # Constraint 7: Red hair directly left of black hair
    idx_red2 = None
    idx_black = None
    for i, house in enumerate(candidate):
        if house[1] == 'red':
            idx_red2 = i
        if house[1] == 'black':
            idx_black = i
    if idx_red2 is None or idx_black is None:
        return False
    if idx_black != idx_red2 + 1:
        return False

    return True

def main():
    names = ['Eric', 'Alice', 'Peter', 'Arnold']
    hair_colors = ['blonde', 'black', 'red', 'brown']
    sports = ['swimming', 'soccer', 'basketball', 'tennis']
    
    perms_names = list(itertools.permutations(names))
    perms_hair = list(itertools.permutations(hair_colors))
    perms_sports = list(itertools.permutations(sports))
    
    solution_candidate = None
    found = False
    
    for n_perm in perms_names:
        if found:
            break
        for h_perm in perms_hair:
            if found:
                break
            for s_perm in perms_sports:
                candidate = []
                for i in range(4):
                    candidate.append((n_perm[i], h_perm[i], s_perm[i]))
                if satisfies(candidate):
                    solution_candidate = candidate
                    found = True
                    break
    
    if solution_candidate is None:
        print(json.dumps({"error": "No solution found"}))
        return
    
    header = ["House", "Name", "Hair Color", "Favorite Sport"]
    rows = []
    for i in range(4):
        house_attrs = solution_candidate[i]
        row = [str(i+1), house_attrs[0], house_attrs[1], house_attrs[2]]
        rows.append(row)
    
    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()