import itertools
import json

def solve_puzzle():
    # Input variables
    houses = [1, 2, 3, 4]  # From left (1) to right (4)
    names = ["Eric", "Arnold", "Peter", "Alice"]
    hair_colors = ["blonde", "black", "brown", "red"]
    music_genres = ["pop", "jazz", "rock", "classical"]

    solutions = []

    # Helper to invert a mapping value->key to key->value
    def invert_map(d):
        return {v: k for k, v in d.items()}

    # Fixed from clues:
    # 5. Classical music is in the first house.
    fixed_music_pos = {"classical": 1}

    # From 2 and 5: classical is directly left of blonde hair -> blonde must be in house 2
    fixed_hair_pos = {"blonde": 2}

    # Enumerate hair assignments
    remaining_hair_colors = [c for c in hair_colors if c not in fixed_hair_pos]
    remaining_hair_houses = [h for h in houses if h not in fixed_hair_pos.values()]
    for hair_perm in itertools.permutations(remaining_hair_houses, len(remaining_hair_colors)):
        hair_pos = dict(fixed_hair_pos)
        hair_pos.update(dict(zip(remaining_hair_colors, hair_perm)))

        # 3. Brown hair is not in the first house.
        if hair_pos["brown"] == 1:
            continue

        # 6. Jazz music is the person who has red hair -> jazz at the red-hair house
        jazz_house = hair_pos["red"]

        # Jazz cannot be in house 1 since classical is there, so red hair cannot be in house 1
        if jazz_house == 1:
            continue

        # Prepare music positions
        music_pos = dict(fixed_music_pos)
        music_pos["jazz"] = jazz_house

        # Remaining music genres to place: rock, pop
        remaining_music = [g for g in music_genres if g not in music_pos]
        remaining_music_houses = [h for h in houses if h not in music_pos.values()]

        for music_perm in itertools.permutations(remaining_music_houses, len(remaining_music)):
            temp_music_pos = dict(music_pos)
            for g, h in zip(remaining_music, music_perm):
                temp_music_pos[g] = h

            # 4. Pop music is not in the third house.
            if temp_music_pos["pop"] == 3:
                continue

            # Names assignment
            for name_perm in itertools.permutations(houses, len(names)):
                name_pos = dict(zip(names, name_perm))

                # 1. Eric has red hair.
                if name_pos["Eric"] != hair_pos["red"]:
                    continue

                # 6. Already enforced via jazz at red hair; redundant with Eric red.

                # 7. Rock music is Arnold.
                if name_pos["Arnold"] != temp_music_pos["rock"]:
                    continue

                # 8. Peter is somewhere to the right of rock (Arnold).
                if not (name_pos["Peter"] > temp_music_pos["rock"]):
                    continue

                # All constraints satisfied
                solutions.append((name_pos, hair_pos, temp_music_pos))

    # Choose the first solution (should be unique for a well-posed puzzle)
    if not solutions:
        raise RuntimeError("No solution found.")
    name_pos, hair_pos, music_pos = solutions[0]

    # Build output rows per house 1..4
    name_at_house = invert_map(name_pos)
    hair_at_house = invert_map(hair_pos)
    music_at_house = invert_map(music_pos)

    rows = []
    for h in houses:
        rows.append([str(h), name_at_house[h], hair_at_house[h], music_at_house[h]])

    output = {
        "solution": {
            "header": ["House", "Name", "HairColor", "MusicGenre"],
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))