import json
from itertools import permutations

def solve_puzzle():
    # Houses numbered 1..6 (left to right)
    houses = [1, 2, 3, 4, 5, 6]

    names = ["Arnold", "Eric", "Peter", "Alice", "Carol", "Bob"]
    genres = ["jazz", "pop", "classical", "rock", "hip hop", "country"]

    # Known fixed positions from clues
    name_pos_fixed = {
        "Eric": 2,        # Clue 4 + 9 imply Eric is at 2 (left of hip hop at 3 and adjacent)
        "Carol": 6        # Clue 3
    }
    genre_pos_fixed = {
        "hip hop": 3,     # Clue 9
        "country": 6      # Clue 5 (country is Carol, who is in house 6)
    }

    remaining_names = [n for n in names if n not in name_pos_fixed]
    used_houses_for_names = set(name_pos_fixed.values())
    available_houses_for_names = [h for h in houses if h not in used_houses_for_names]

    solutions = []

    for perm in permutations(available_houses_for_names, len(remaining_names)):
        name_pos = dict(name_pos_fixed)
        valid = True
        for n, h in zip(remaining_names, perm):
            name_pos[n] = h

        # Name-based constraints:
        # Clue 6: Arnold is not in the fifth house.
        if name_pos["Arnold"] == 5:
            continue
        # Clue 10: There is one house between Peter and Bob.
        if abs(name_pos["Peter"] - name_pos["Bob"]) != 2:
            continue
        # Clue 7 + 8: Arnold is somewhere to the right of the person who loves pop music; pop is Peter.
        if not (name_pos["Arnold"] > name_pos["Peter"]):
            continue
        # Peter cannot be at house of hip hop (3), since pop (Peter) would conflict with hip hop in the same house.
        if name_pos["Peter"] == genre_pos_fixed["hip hop"]:
            continue
        # Eric and hip hop are adjacent with Eric to the left (Clues 2,4,9) - already ensured by fixed positions,
        # but keep the check general:
        if not (abs(name_pos["Eric"] - genre_pos_fixed["hip hop"]) == 1 and name_pos["Eric"] < genre_pos_fixed["hip hop"]):
            continue
        # Carol is in 6 (already fixed)

        # Now assign music genres
        # Start with fixed genres
        genre_pos = dict(genre_pos_fixed)

        # Clue 8: Pop is Peter
        pop_house = name_pos["Peter"]
        # Ensure no conflict
        if pop_house in genre_pos.values():
            continue
        genre_pos["pop"] = pop_house

        # Clue 1: Bob is directly left of the person who loves jazz.
        bob_house = name_pos["Bob"]
        jazz_house = bob_house + 1
        if jazz_house not in houses:
            continue
        # Ensure no conflict with other fixed genres
        if jazz_house in genre_pos.values():
            continue
        genre_pos["jazz"] = jazz_house

        # Remaining genres to place: classical, rock
        remaining_genres = [g for g in genres if g not in genre_pos]
        assigned_houses = set(genre_pos.values())
        remaining_houses = [h for h in houses if h not in assigned_houses]

        # There should be exactly two remaining houses and genres
        if len(remaining_genres) != 2 or len(remaining_houses) != 2:
            continue

        # Try both ways to assign remaining genres, respecting Clue 11: Rock not in the fifth house.
        for rem_perm in permutations(remaining_houses, len(remaining_genres)):
            gpos = dict(genre_pos)
            for g, h in zip(remaining_genres, rem_perm):
                gpos[g] = h

            # Clue 11: Rock not in the fifth house.
            if gpos["rock"] == 5:
                continue

            # All constraints satisfied - record solution
            house_to_name = {h: None for h in houses}
            for n, h in name_pos.items():
                house_to_name[h] = n

            house_to_genre = {h: None for h in houses}
            for g, h in gpos.items():
                house_to_genre[h] = g

            # Final verification of all clues (safety check)
            def check_all():
                # 1. Bob is directly left of jazz
                if not (house_to_name[bob_house] == "Bob" and house_to_genre.get(bob_house + 1) == "jazz"):
                    return False
                # 2. Eric left of hip hop
                if not (name_pos["Eric"] < gpos["hip hop"]):
                    return False
                # 3. Carol in sixth
                if not (name_pos["Carol"] == 6):
                    return False
                # 4. Eric adjacent to hip hop
                if not (abs(name_pos["Eric"] - gpos["hip hop"]) == 1):
                    return False
                # 5. Country is Carol
                if not (house_to_genre[name_pos["Carol"]] == "country"):
                    return False
                # 6. Arnold not in fifth
                if name_pos["Arnold"] == 5:
                    return False
                # 7. Arnold right of pop
                if not (name_pos["Arnold"] > gpos["pop"]):
                    return False
                # 8. Pop is Peter
                if not (gpos["pop"] == name_pos["Peter"]):
                    return False
                # 9. Hip hop is in third
                if gpos["hip hop"] != 3:
                    return False
                # 10. One house between Peter and Bob
                if abs(name_pos["Peter"] - name_pos["Bob"]) != 2:
                    return False
                # 11. Rock not in fifth
                if gpos["rock"] == 5:
                    return False
                return True

            if check_all():
                solutions.append((house_to_name, house_to_genre))

        # If a solution is found, we can stop exploring further permutations
        if solutions:
            break

    if not solutions:
        raise RuntimeError("No solution found.")

    # Assume unique or take the first found
    house_to_name, house_to_genre = solutions[0]

    # Build JSON structure
    rows = []
    for h in houses:
        rows.append([str(h), house_to_name[h], house_to_genre[h]])

    result = {
        "solution": {
            "header": ["House", "Name", "MusicGenre"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))