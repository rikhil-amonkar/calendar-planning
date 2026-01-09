import json

def solve_with_python_constraint():
    try:
        from constraint import Problem, AllDifferentConstraint
    except ImportError:
        return None  # Fallback will handle

    houses = [1, 2, 3]

    Names = ["Arnold", "Eric", "Peter"]
    Flowers = ["carnations", "lilies", "daffodils"]
    HairColors = ["black", "brown", "blonde"]
    Sports = ["soccer", "basketball", "tennis"]
    HouseStyles = ["colonial", "ranch", "victorian"]
    Pets = ["fish", "dog", "cat"]

    def varmap(prefix, values):
        return {v: f"{prefix}_{v}" for v in values}

    name_vars = varmap("Name", Names)
    flower_vars = varmap("Flower", Flowers)
    hair_vars = varmap("Hair", HairColors)
    sport_vars = varmap("Sport", Sports)
    style_vars = varmap("Style", HouseStyles)
    pet_vars = varmap("Pet", Pets)

    problem = Problem()

    for v in list(name_vars.values()) + list(flower_vars.values()) + list(hair_vars.values()) + \
             list(sport_vars.values()) + list(style_vars.values()) + list(pet_vars.values()):
        problem.addVariable(v, houses)

    problem.addConstraint(AllDifferentConstraint(), list(name_vars.values()))
    problem.addConstraint(AllDifferentConstraint(), list(flower_vars.values()))
    problem.addConstraint(AllDifferentConstraint(), list(hair_vars.values()))
    problem.addConstraint(AllDifferentConstraint(), list(sport_vars.values()))
    problem.addConstraint(AllDifferentConstraint(), list(style_vars.values()))
    problem.addConstraint(AllDifferentConstraint(), list(pet_vars.values()))

    # Clue 1: cat <-> soccer
    problem.addConstraint(lambda c, s: c == s, (pet_vars["cat"], sport_vars["soccer"]))
    # Clue 2: blonde hair is in the second house
    problem.addConstraint(lambda x: x == 2, (hair_vars["blonde"],))
    # Clue 3: daffodils <-> blonde hair
    problem.addConstraint(lambda f, h: f == h, (flower_vars["daffodils"], hair_vars["blonde"]))
    # Clue 4: Peter <-> basketball
    problem.addConstraint(lambda n, s: n == s, (name_vars["Peter"], sport_vars["basketball"]))
    # Clue 5: Arnold directly left of ranch
    problem.addConstraint(lambda a, r: a + 1 == r, (name_vars["Arnold"], style_vars["ranch"]))
    # Clue 6: dog <-> basketball
    problem.addConstraint(lambda p, s: p == s, (pet_vars["dog"], sport_vars["basketball"]))
    # Clue 7: carnations directly left of blonde hair
    problem.addConstraint(lambda c, b: c == b - 1, (flower_vars["carnations"], hair_vars["blonde"]))
    # Clue 8: soccer is in the third house
    problem.addConstraint(lambda x: x == 3, (sport_vars["soccer"],))
    # Clue 9: Arnold is somewhere to the left of black hair
    problem.addConstraint(lambda a, bl: a < bl, (name_vars["Arnold"], hair_vars["black"]))
    # Clue 10: colonial is in the third house
    problem.addConstraint(lambda x: x == 3, (style_vars["colonial"],))

    solutions = problem.getSolutions()
    if not solutions:
        return None

    sol = solutions[0]

    def find_value(category_vars, house_num):
        for val, var in category_vars.items():
            if sol[var] == house_num:
                return val
        return None

    rows = []
    for h in houses:
        row = [
            str(h),
            find_value(name_vars, h),
            find_value(flower_vars, h),
            find_value(hair_vars, h),
            find_value(sport_vars, h),
            find_value(style_vars, h),
            find_value(pet_vars, h),
        ]
        rows.append(row)

    return {
        "solution": {
            "header": ["House", "Name", "Flower", "HairColor", "FavoriteSport", "HouseStyle", "Pet"],
            "rows": rows
        }
    }

def solve_with_fallback():
    # Fallback generic solver using permutations if python-constraint is unavailable
    import itertools

    houses = [1, 2, 3]

    Names = ["Arnold", "Eric", "Peter"]
    Flowers = ["carnations", "lilies", "daffodils"]
    HairColors = ["black", "brown", "blonde"]
    Sports = ["soccer", "basketball", "tennis"]
    HouseStyles = ["colonial", "ranch", "victorian"]
    Pets = ["fish", "dog", "cat"]

    perms = list(itertools.permutations(houses))

    for name_pos in perms:
        pos_name = dict(zip(Names, name_pos))
        # Clue 5: Arnold directly left of ranch (depends on style), defer
        # Clue 9: Arnold to the left of black hair (depends on hair), defer

        for hair_pos in perms:
            pos_hair = dict(zip(HairColors, hair_pos))
            # Clue 2: blonde is house 2
            if pos_hair["blonde"] != 2:
                continue
            # Clue 9: Arnold somewhere to the left of black hair
            if not (pos_name["Arnold"] < pos_hair["black"]):
                continue

            for flower_pos in perms:
                pos_flower = dict(zip(Flowers, flower_pos))
                # Clue 3: daffodils <-> blonde hair
                if pos_flower["daffodils"] != pos_hair["blonde"]:
                    continue
                # Clue 7: carnations directly left of blonde hair
                if pos_flower["carnations"] != pos_hair["blonde"] - 1:
                    continue

                for sport_pos in perms:
                    pos_sport = dict(zip(Sports, sport_pos))
                    # Clue 8: soccer is in the third house
                    if pos_sport["soccer"] != 3:
                        continue
                    # Clue 4: Peter <-> basketball
                    if pos_name["Peter"] != pos_sport["basketball"]:
                        continue

                    for style_pos in perms:
                        pos_style = dict(zip(HouseStyles, style_pos))
                        # Clue 10: colonial is in the third house
                        if pos_style["colonial"] != 3:
                            continue
                        # Clue 5: Arnold directly left of ranch
                        if pos_name["Arnold"] + 1 != pos_style["ranch"]:
                            continue

                        for pet_pos in perms:
                            pos_pet = dict(zip(Pets, pet_pos))
                            # Clue 1: cat <-> soccer
                            if pos_pet["cat"] != pos_sport["soccer"]:
                                continue
                            # Clue 6: dog <-> basketball
                            if pos_pet["dog"] != pos_sport["basketball"]:
                                continue

                            # Build rows
                            rows = []
                            for h in houses:
                                # Find values by house
                                name = next(k for k, v in pos_name.items() if v == h)
                                flower = next(k for k, v in pos_flower.items() if v == h)
                                hair = next(k for k, v in pos_hair.items() if v == h)
                                sport = next(k for k, v in pos_sport.items() if v == h)
                                style = next(k for k, v in pos_style.items() if v == h)
                                pet = next(k for k, v in pos_pet.items() if v == h)
                                rows.append([str(h), name, flower, hair, sport, style, pet])

                            return {
                                "solution": {
                                    "header": ["House", "Name", "Flower", "HairColor", "FavoriteSport", "HouseStyle", "Pet"],
                                    "rows": rows
                                }
                            }
    return None

def main():
    result = solve_with_python_constraint()
    if result is None:
        result = solve_with_fallback()
    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()