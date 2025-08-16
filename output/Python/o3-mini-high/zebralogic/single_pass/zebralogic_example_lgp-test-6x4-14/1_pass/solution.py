#!/usr/bin/env python3
import json
import sys
import copy

names_all = ["Eric", "Bob", "Peter", "Alice", "Arnold", "Carol"]
cars_all = ["ford f150", "honda civic", "toyota camry", "tesla model 3", "chevrolet silverado", "bmw 3 series"]
mothers_all = ["Sarah", "Penny", "Holly", "Aniya", "Kailyn", "Janelle"]
hobbies_all = ["photography", "cooking", "knitting", "gardening", "woodworking", "painting"]

# Global variable to store a found solution
solution_found = None

def global_constraints(sol):
    # sol is a list of 6 tuples: (name, car, mother, hobby) for houses 0..5.
    # Houses are numbered 1..6 (index+1).
    
    # Constraint: "Alice is somewhere to the right of the person who owns a Ford F-150."
    # Ford F-150 is fixed to house 4 (index3). So if any house has name "Alice", its index must be > 3.
    for i, (n, car, m, h) in enumerate(sol):
        if n == "Alice" and i <= 3:
            return False

    # Constraint: "There is one house between The person whose mother's name is Sarah and the person who loves cooking."
    # Sarah must be in house 4 (index3), so cooking must be in house 2 (index1) or house 6 (index5).
    idx_cooking = None
    for i, (_, _, _, h) in enumerate(sol):
        if h == "cooking":
            idx_cooking = i
            break
    if idx_cooking is None or abs((idx_cooking+1) - 4) != 2:
        return False

    # Constraint: "The person whose mother's name Penny is somewhere to the right of the person who enjoys knitting."
    idx_knitting = None
    idx_penny = None
    for i, (_, _, m, h) in enumerate(sol):
        if h == "knitting":
            idx_knitting = i
        if m == "Penny":
            idx_penny = i
    if idx_knitting is None or idx_penny is None or idx_penny <= idx_knitting:
        return False

    # Constraint: "The person whose mother's name Aniya is somewhere to the right of the person who owns a Honda Civic."
    # Note: by pairing, any house with mother Aniya should have car "chevrolet silverado".
    idx_honda = None
    idx_aniya = None
    for i, (_, car, m, _) in enumerate(sol):
        if car == "honda civic":
            idx_honda = i
        if m == "Aniya":  # should appear on the chevrolet silverado house.
            idx_aniya = i
    if idx_honda is None or idx_aniya is None or idx_honda >= idx_aniya:
        return False

    # Constraint: "The woodworking hobbyist is somewhere to the left of the person who enjoys knitting."
    idx_wood = None
    idx_knit = None
    for i, (_, _, _, h) in enumerate(sol):
        if h == "woodworking":
            idx_wood = i
        if h == "knitting":
            idx_knit = i
    if idx_wood is None or idx_knit is None or idx_wood >= idx_knit:
        return False

    # Constraint: "The person whose mother's name Holly is directly left of the person who enjoys knitting."
    # Also "Eric is directly left of the person who enjoys knitting."
    # There must be a house where the hobby is knitting and its immediate left house has mother Holly and name Eric.
    for i, (_, _, _, h) in enumerate(sol):
        if h == "knitting":
            if i == 0:
                return False
            prev = sol[i-1]
            if prev[0] != "Eric" or prev[2] != "Holly" or prev[3] != "gardening":
                return False

    return True

def backtrack(i, sol, avail_names, avail_cars, avail_mothers, avail_hobbies):
    global solution_found
    if solution_found is not None:
        return
    if i == 6:
        if global_constraints(sol):
            solution_found = copy.deepcopy(sol)
        return

    # For house i, try all combinations from the available items.
    for n in avail_names:
        # If name is "Alice", it must be placed to the right of house4 (i > 3, since house4 is index3).
        if n == "Alice" and i < 4:
            continue
        for c in avail_cars:
            # Fixed car positions:
            if i == 5 and c != "toyota camry":
                continue
            if i != 5 and c == "toyota camry":
                continue
            if i == 3 and c != "ford f150":
                continue
            if i != 3 and c == "ford f150":
                continue
            # "chevrolet silverado" is not allowed in house2 (index1)
            if i == 1 and c == "chevrolet silverado":
                continue
            for m in avail_mothers:
                # Fixed mother positions:
                if i == 5 and m != "Kailyn":
                    continue
                if i != 5 and m == "Kailyn":
                    continue
                if i == 3 and m != "Sarah":
                    continue
                if i != 3 and m == "Sarah":
                    continue
                for h in avail_hobbies:
                    # If h is "cooking", allowed only in house2 (index1) or house6 (index5).
                    if h == "cooking" and i not in [1, 5]:
                        continue
                    # Build candidate tuple for house i.
                    candidate = (n, c, m, h)

                    # Enforce immediate pairing constraints:
                    # If car is "honda civic", then name must be "Arnold"
                    if c == "honda civic" and n != "Arnold":
                        continue
                    # If car is "bmw 3 series", then name must be "Bob"
                    if c == "bmw 3 series" and n != "Bob":
                        continue
                    # If car is "chevrolet silverado", then mother must be "Aniya"
                    if c == "chevrolet silverado" and m != "Aniya":
                        continue
                    # If name is "Eric", hobby must be "gardening"
                    if n == "Eric" and h != "gardening":
                        continue
                    # If name is "Carol", hobby must be "photography"
                    if n == "Carol" and h != "photography":
                        continue

                    # If this house's hobby is "knitting", then its immediate left house must exist and satisfy:
                    #   name == "Eric", mother == "Holly", and hobby == "gardening"
                    if h == "knitting":
                        if i == 0:
                            continue
                        prev = sol[i-1]
                        if prev[0] != "Eric" or prev[2] != "Holly" or prev[3] != "gardening":
                            continue

                    # Create new solution state.
                    sol.append(candidate)
                    new_avail_names = avail_names.copy()
                    new_avail_names.remove(n)
                    new_avail_cars = avail_cars.copy()
                    new_avail_cars.remove(c)
                    new_avail_mothers = avail_mothers.copy()
                    new_avail_mothers.remove(m)
                    new_avail_hobbies = avail_hobbies.copy()
                    new_avail_hobbies.remove(h)

                    backtrack(i+1, sol, new_avail_names, new_avail_cars, new_avail_mothers, new_avail_hobbies)
                    if solution_found is not None:
                        return
                    sol.pop()

def main():
    global solution_found
    sol = []
    backtrack(0, sol, names_all, cars_all, mothers_all, hobbies_all)
    if solution_found is None:
        result = {"solution": {"header": ["House", "Name", "CarModel", "Mother", "Hobby"], "rows": []}}
    else:
        # Format the solution rows with house numbers as strings (1-indexed)
        rows = []
        for i, (n, c, m, h) in enumerate(solution_found):
            rows.append([str(i+1), n, c, m, h])
        result = {"solution": {"header": ["House", "Name", "CarModel", "Mother", "Hobby"], "rows": rows}}
    json_output = json.dumps(result, indent=2)
    sys.stdout.write(json_output)

if __name__ == '__main__':
    main()