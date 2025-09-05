import json
from itertools import product

def solve_puzzle():
    # Puzzle data
    houses = list(range(6))  # 0..5 represent houses 1..6
    Names = ["Eric", "Bob", "Peter", "Alice", "Arnold", "Carol"]
    Cars = ["ford f150", "honda civic", "toyota camry", "tesla model 3", "chevrolet silverado", "bmw 3 series"]
    Mothers = ["Sarah", "Penny", "Holly", "Aniya", "Kailyn", "Janelle"]
    Hobbies = ["photography", "cooking", "knitting", "gardening", "woodworking", "painting"]

    # Initialize assignments per house
    assignment = [{"Name": None, "Car": None, "Mother": None, "Hobby": None} for _ in houses]
    used_name = set()
    used_car = set()
    used_mother = set()
    used_hobby = set()

    # Apply direct fixed constraints:
    # 1. Toyota Camry is in the sixth house (index 5)
    assignment[5]["Car"] = "toyota camry"
    used_car.add("toyota camry")
    # 7. Mother Kailyn is in the sixth house
    assignment[5]["Mother"] = "Kailyn"
    used_mother.add("Kailyn")

    # Helper: build position maps for currently assigned items
    def build_pos_maps():
        pos_by_name = {}
        pos_by_car = {}
        pos_by_mother = {}
        pos_by_hobby = {}
        for i, a in enumerate(assignment):
            if a["Name"] is not None: pos_by_name[a["Name"]] = i
            if a["Car"] is not None: pos_by_car[a["Car"]] = i
            if a["Mother"] is not None: pos_by_mother[a["Mother"]] = i
            if a["Hobby"] is not None: pos_by_hobby[a["Hobby"]] = i
        return pos_by_name, pos_by_car, pos_by_mother, pos_by_hobby

    # Check all constraints that can be evaluated with current partial assignment
    def check_global_constraints():
        pos_by_name, pos_by_car, pos_by_mother, pos_by_hobby = build_pos_maps()

        # 1. Toyota Camry is in the sixth house.
        if "toyota camry" in pos_by_car and pos_by_car["toyota camry"] != 5:
            return False

        # 2. Carol is the photography enthusiast.
        if "Carol" in pos_by_name and "photography" in pos_by_hobby:
            if pos_by_name["Carol"] != pos_by_hobby["photography"]:
                return False

        # 3. Chevy Silverado is the person whose mother's name is Aniya. (equivalence)
        if "chevrolet silverado" in pos_by_car and "Aniya" in pos_by_mother:
            if pos_by_car["chevrolet silverado"] != pos_by_mother["Aniya"]:
                return False

        # 4. Chevy Silverado not in the second house (index 1).
        if "chevrolet silverado" in pos_by_car and pos_by_car["chevrolet silverado"] == 1:
            return False

        # 5. Ford F-150 is the person whose mother's name is Sarah. (equivalence)
        if "ford f150" in pos_by_car and "Sarah" in pos_by_mother:
            if pos_by_car["ford f150"] != pos_by_mother["Sarah"]:
                return False

        # 6. BMW 3 Series is Bob.
        if "bmw 3 series" in pos_by_car and "Bob" in pos_by_name:
            if pos_by_car["bmw 3 series"] != pos_by_name["Bob"]:
                return False

        # 7. Mother Kailyn is in the sixth house.
        if "Kailyn" in pos_by_mother and pos_by_mother["Kailyn"] != 5:
            return False

        # 8. Eric is directly left of the person who enjoys knitting.
        if "Eric" in pos_by_name and "knitting" in pos_by_hobby:
            if pos_by_name["Eric"] != pos_by_hobby["knitting"] - 1:
                return False

        # 9. One house between Sarah and Toyota Camry.
        if "Sarah" in pos_by_mother and "toyota camry" in pos_by_car:
            if abs(pos_by_mother["Sarah"] - pos_by_car["toyota camry"]) != 2:
                return False

        # 10. Penny is somewhere to the right of the knitter.
        if "Penny" in pos_by_mother and "knitting" in pos_by_hobby:
            if not (pos_by_mother["Penny"] > pos_by_hobby["knitting"]):
                return False

        # 11. Aniya is somewhere to the right of the Honda Civic.
        if "Aniya" in pos_by_mother and "honda civic" in pos_by_car:
            if not (pos_by_mother["Aniya"] > pos_by_car["honda civic"]):
                return False

        # 12. Alice is somewhere to the right of the Ford F-150.
        if "Alice" in pos_by_name and "ford f150" in pos_by_car:
            if not (pos_by_name["Alice"] > pos_by_car["ford f150"]):
                return False

        # 13. Eric is the person who enjoys gardening.
        if "Eric" in pos_by_name and "gardening" in pos_by_hobby:
            if pos_by_name["Eric"] != pos_by_hobby["gardening"]:
                return False

        # 14. Woodworking left of knitting.
        if "woodworking" in pos_by_hobby and "knitting" in pos_by_hobby:
            if not (pos_by_hobby["woodworking"] < pos_by_hobby["knitting"]):
                return False

        # 15. One house between Sarah and cooking.
        if "Sarah" in pos_by_mother and "cooking" in pos_by_hobby:
            if abs(pos_by_mother["Sarah"] - pos_by_hobby["cooking"]) != 2:
                return False

        # 16. Honda Civic is Arnold.
        if "honda civic" in pos_by_car and "Arnold" in pos_by_name:
            if pos_by_car["honda civic"] != pos_by_name["Arnold"]:
                return False

        # 17. Holly directly left of knitting.
        if "Holly" in pos_by_mother and "knitting" in pos_by_hobby:
            if pos_by_mother["Holly"] != pos_by_hobby["knitting"] - 1:
                return False

        # Additional derived equivalences and consistency checks:

        # Carol <-> photography
        if "Carol" in pos_by_name and assignment[pos_by_name["Carol"]]["Hobby"] is not None:
            if assignment[pos_by_name["Carol"]]["Hobby"] != "photography":
                return False
        if "photography" in pos_by_hobby and assignment[pos_by_hobby["photography"]]["Name"] is not None:
            if assignment[pos_by_hobby["photography"]]["Name"] != "Carol":
                return False

        # Eric <-> gardening
        if "Eric" in pos_by_name and assignment[pos_by_name["Eric"]]["Hobby"] is not None:
            if assignment[pos_by_name["Eric"]]["Hobby"] != "gardening":
                return False
        if "gardening" in pos_by_hobby and assignment[pos_by_hobby["gardening"]]["Name"] is not None:
            if assignment[pos_by_hobby["gardening"]]["Name"] != "Eric":
                return False

        # Bob <-> BMW
        if "Bob" in pos_by_name and assignment[pos_by_name["Bob"]]["Car"] is not None:
            if assignment[pos_by_name["Bob"]]["Car"] != "bmw 3 series":
                return False
        if "bmw 3 series" in pos_by_car and assignment[pos_by_car["bmw 3 series"]]["Name"] is not None:
            if assignment[pos_by_car["bmw 3 series"]]["Name"] != "Bob":
                return False

        # Arnold <-> Civic
        if "Arnold" in pos_by_name and assignment[pos_by_name["Arnold"]]["Car"] is not None:
            if assignment[pos_by_name["Arnold"]]["Car"] != "honda civic":
                return False
        if "honda civic" in pos_by_car and assignment[pos_by_car["honda civic"]]["Name"] is not None:
            if assignment[pos_by_car["honda civic"]]["Name"] != "Arnold":
                return False

        # F-150 <-> Sarah
        if "ford f150" in pos_by_car and assignment[pos_by_car["ford f150"]]["Mother"] is not None:
            if assignment[pos_by_car["ford f150"]]["Mother"] != "Sarah":
                return False
        if "Sarah" in pos_by_mother and assignment[pos_by_mother["Sarah"]]["Car"] is not None:
            if assignment[pos_by_mother["Sarah"]]["Car"] != "ford f150":
                return False

        # Silverado <-> Aniya
        if "chevrolet silverado" in pos_by_car and assignment[pos_by_car["chevrolet silverado"]]["Mother"] is not None:
            if assignment[pos_by_car["chevrolet silverado"]]["Mother"] != "Aniya":
                return False
        if "Aniya" in pos_by_mother and assignment[pos_by_mother["Aniya"]]["Car"] is not None:
            if assignment[pos_by_mother["Aniya"]]["Car"] != "chevrolet silverado":
                return False

        # Eric and Holly must be same house (derived from 8 and 17)
        if "Eric" in pos_by_name and "Holly" in pos_by_mother and "knitting" in pos_by_hobby:
            if not (pos_by_name["Eric"] == pos_by_mother["Holly"] == pos_by_hobby["knitting"] - 1):
                return False

        # Local neighbor consistency for assigned neighbors:
        for i, a in enumerate(assignment):
            # If Holly is assigned in house i, ensure right neighbor (if assigned) has knitting
            if a["Mother"] == "Holly":
                if i == 5:
                    return False
                if assignment[i+1]["Hobby"] is not None and assignment[i+1]["Hobby"] != "knitting":
                    return False
            # If Eric is assigned in house i, ensure right neighbor (if assigned) has knitting and hobby gardening here
            if a["Name"] == "Eric":
                if i == 5:
                    return False
                if a["Hobby"] is not None and a["Hobby"] != "gardening":
                    return False
                if assignment[i+1]["Hobby"] is not None and assignment[i+1]["Hobby"] != "knitting":
                    return False
            # Knitting cannot be in house 0 or 5 due to left neighbor and Penny to the right constraints
            if a["Hobby"] == "knitting":
                if i == 0 or i == 5:
                    return False
                # left neighbor must be Eric and Holly if assigned
                if assignment[i-1]["Name"] is not None and assignment[i-1]["Name"] != "Eric":
                    return False
                if assignment[i-1]["Mother"] is not None and assignment[i-1]["Mother"] != "Holly":
                    return False

            # Silverado not in house 1 (index 1)
            if a["Car"] == "chevrolet silverado" and i == 1:
                return False

            # Kailyn must be in house 5
            if a["Mother"] == "Kailyn" and i != 5:
                return False

            # If F150 here, mother must be Sarah (and vice versa)
            if a["Car"] == "ford f150" and a["Mother"] is not None and a["Mother"] != "Sarah":
                return False
            if a["Mother"] == "Sarah" and a["Car"] is not None and a["Car"] != "ford f150":
                return False

            # If BMW here, name must be Bob (and vice versa)
            if a["Car"] == "bmw 3 series" and a["Name"] is not None and a["Name"] != "Bob":
                return False
            if a["Name"] == "Bob" and a["Car"] is not None and a["Car"] != "bmw 3 series":
                return False

            # If Honda here, name must be Arnold (and vice versa)
            if a["Car"] == "honda civic" and a["Name"] is not None and a["Name"] != "Arnold":
                return False
            if a["Name"] == "Arnold" and a["Car"] is not None and a["Car"] != "honda civic":
                return False

            # Carol is photography (local)
            if a["Name"] == "Carol" and a["Hobby"] is not None and a["Hobby"] != "photography":
                return False
            if a["Hobby"] == "photography" and a["Name"] is not None and a["Name"] != "Carol":
                return False

            # Eric is gardening (local)
            if a["Name"] == "Eric" and a["Hobby"] is not None and a["Hobby"] != "gardening":
                return False
            if a["Hobby"] == "gardening" and a["Name"] is not None and a["Name"] != "Eric":
                return False

        return True

    # Generate candidate tuples for a house based on current state (with local pruning)
    def generate_candidates(h):
        if assignment[h]["Name"] is not None and assignment[h]["Car"] is not None and assignment[h]["Mother"] is not None and assignment[h]["Hobby"] is not None:
            return [(assignment[h]["Name"], assignment[h]["Car"], assignment[h]["Mother"], assignment[h]["Hobby"])]

        # Compute domains
        name_domain = [n for n in Names if n not in used_name]
        car_domain = [c for c in Cars if c not in used_car]
        mother_domain = [m for m in Mothers if m not in used_mother]
        hobby_domain = [hb for hb in Hobbies if hb not in used_hobby]

        # Apply house-specific unary constraints
        # Car: Camry only at house 5; else cannot be Camry
        if h == 5:
            car_domain = ["toyota camry"]
        else:
            car_domain = [c for c in car_domain if c != "toyota camry"]

        # Mother: Kailyn only at house 5; else cannot be Kailyn
        if h == 5:
            mother_domain = ["Kailyn"]
        else:
            mother_domain = [m for m in mother_domain if m != "Kailyn"]

        # Silverado not in house 1 (index 1)
        if h == 1:
            car_domain = [c for c in car_domain if c != "chevrolet silverado"]

        # Knitting cannot be at house 0 or 5 (left neighbor required and Penny to the right)
        if h == 0 or h == 5:
            hobby_domain = [hb for hb in hobby_domain if hb != "knitting"]

        # Eric cannot be at last house (must be left of knitter)
        if h == 5:
            name_domain = [n for n in name_domain if n != "Eric"]

        # Build candidates with progressive consistency checks
        candidates = []
        for name in name_domain:
            # Name-car and name-hobby and name-mother link filters (partial)
            # Name Eric implies mother Holly and hobby gardening, and not last house (already filtered)
            # Name Bob implies car BMW
            # Name Arnold implies car Civic
            # Name Carol implies hobby photography
            # Enforce Eric/Holly link both ways (derived)
            # We'll enforce in loop.

            for mother in mother_domain:
                # Eric <-> Holly (derived from 8 & 17)
                if (name == "Eric" and mother != "Holly") or (mother == "Holly" and name != "Eric"):
                    continue
                # Mother Holly cannot be in last house (no right neighbor)
                if mother == "Holly" and h == 5:
                    continue

                # If mother is Sarah, enforce distance to Camry (house 5) to be 2; i.e., h == 3
                if mother == "Sarah":
                    if abs(h - 5) != 2:
                        continue

                for hobby in hobby_domain:
                    # Name-Hobby links
                    if (name == "Carol" and hobby != "photography") or (hobby == "photography" and name != "Carol"):
                        continue
                    if (name == "Eric" and hobby != "gardening") or (hobby == "gardening" and name != "Eric"):
                        continue

                    # Knitting adjacency local checks
                    if hobby == "knitting":
                        if h == 0 or h == 5:
                            continue
                        # Left neighbor must be Eric and Holly if already assigned
                        left = assignment[h-1]
                        if left["Name"] is not None and left["Name"] != "Eric":
                            continue
                        if left["Mother"] is not None and left["Mother"] != "Holly":
                            continue
                    # If mother is Holly, right neighbor must be knitting if already assigned
                    if mother == "Holly":
                        # ensure right neighbor exists
                        if h == 5:
                            continue
                        right = assignment[h+1]
                        if right["Hobby"] is not None and right["Hobby"] != "knitting":
                            continue

                    # One house between Sarah and cooking (local adjacency if one side already placed)
                    if mother == "Sarah":
                        # cooking must be two away; if cooking already assigned, check now
                        for idx, a in enumerate(assignment):
                            if a["Hobby"] == "cooking":
                                if abs(h - idx) != 2:
                                    break
                        else:
                            pass  # no cooking assigned yet
                    if hobby == "cooking":
                        for idx, a in enumerate(assignment):
                            if a["Mother"] == "Sarah":
                                if abs(h - idx) != 2:
                                    break
                        else:
                            pass

                    # Woodworking cannot be at last house if knitting not to the right somewhere; soft check:
                    if hobby == "woodworking":
                        # If all houses to right are assigned with non-knitting hobbies, fail
                        to_right_has_potential_knit = False
                        for r in range(h+1, 6):
                            if assignment[r]["Hobby"] is None or assignment[r]["Hobby"] == "knitting":
                                to_right_has_potential_knit = True
                                break
                        if not to_right_has_potential_knit:
                            continue

                    # Now cars
                    for car in car_domain:
                        # Name-Car links
                        if (name == "Bob" and car != "bmw 3 series") or (car == "bmw 3 series" and name != "Bob"):
                            continue
                        if (name == "Arnold" and car != "honda civic") or (car == "honda civic" and name != "Arnold"):
                            continue

                        # Car-Mother links
                        if (car == "ford f150" and mother != "Sarah") or (mother == "Sarah" and car != "ford f150"):
                            continue
                        if (car == "chevrolet silverado" and mother != "Aniya") or (mother == "Aniya" and car != "chevrolet silverado"):
                            continue

                        # Silverado not in house 1
                        if car == "chevrolet silverado" and h == 1:
                            continue

                        # Alice cannot be same house as F-150 (since Alice is to the right of F-150)
                        if name == "Alice" and car == "ford f150":
                            continue

                        # Passed local checks; add candidate
                        candidates.append((name, car, mother, hobby))
        return candidates

    # Choose next house to assign using MRV heuristic on candidate count
    def select_unassigned_house():
        best_house = None
        best_candidates = None
        best_count = None
        for h in houses:
            a = assignment[h]
            if None in (a["Name"], a["Car"], a["Mother"], a["Hobby"]):
                cands = generate_candidates(h)
                if best_house is None or len(cands) < best_count:
                    best_house = h
                    best_candidates = cands
                    best_count = len(cands)
                if best_count == 0:
                    break
        return best_house, best_candidates

    solution_found = [False]

    def backtrack():
        if not check_global_constraints():
            return False

        # Check if complete
        complete = True
        for a in assignment:
            if None in (a["Name"], a["Car"], a["Mother"], a["Hobby"]):
                complete = False
                break
        if complete:
            solution_found[0] = True
            return True

        h, candidates = select_unassigned_house()
        if candidates is None or len(candidates) == 0:
            return False

        for (name, car, mother, hobby) in candidates:
            # Save old values
            old = assignment[h].copy()
            # Assign
            # We must ensure we don't double-assign used sets for values already present in this house (should be None or same)
            # Remove currently assigned from used_* if any (shouldn't be, but safe)
            for key, val, used_set in [("Name", assignment[h]["Name"], used_name),
                                       ("Car", assignment[h]["Car"], used_car),
                                       ("Mother", assignment[h]["Mother"], used_mother),
                                       ("Hobby", assignment[h]["Hobby"], used_hobby)]:
                if val is not None:
                    used_set.discard(val)

            # Attempt assignment
            # Check if chosen values are already used elsewhere
            if name in used_name or car in used_car or mother in used_mother or hobby in used_hobby:
                # restore old
                assignment[h] = old
                for key, val, used_set in [("Name", assignment[h]["Name"], used_name),
                                           ("Car", assignment[h]["Car"], used_car),
                                           ("Mother", assignment[h]["Mother"], used_mother),
                                           ("Hobby", assignment[h]["Hobby"], used_hobby)]:
                    if val is not None:
                        used_set.add(val)
                continue

            assignment[h]["Name"] = name
            assignment[h]["Car"] = car
            assignment[h]["Mother"] = mother
            assignment[h]["Hobby"] = hobby

            used_name.add(name)
            used_car.add(car)
            used_mother.add(mother)
            used_hobby.add(hobby)

            if check_global_constraints():
                if backtrack():
                    return True

            # Undo
            used_name.discard(name)
            used_car.discard(car)
            used_mother.discard(mother)
            used_hobby.discard(hobby)
            assignment[h] = old
            # Re-add old used if present
            if old["Name"] is not None: used_name.add(old["Name"])
            if old["Car"] is not None: used_car.add(old["Car"])
            if old["Mother"] is not None: used_mother.add(old["Mother"])
            if old["Hobby"] is not None: used_hobby.add(old["Hobby"])

        return False

    backtrack()

    if not solution_found[0]:
        raise RuntimeError("No solution found")

    # Prepare JSON output
    header = ["House", "Name", "CarModel", "Mother", "Hobby"]
    rows = []
    for i in range(6):
        a = assignment[i]
        rows.append([str(i+1), a["Name"], a["Car"], a["Mother"], a["Hobby"]])

    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))