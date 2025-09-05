import json
from itertools import permutations

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Arnold', 'Eric', 'Peter', 'Alice', 'Carol', 'Bob']
    musics = ['jazz', 'pop', 'classical', 'rock', 'hip hop', 'country']

    # Fixed from clues:
    # - Carol is in the 6th house (clue 3)
    # - Hip hop is in the 3rd house (clue 9)
    # - Carol loves country (clue 5)
    # - Pop is Peter's favorite (clue 8)
    fixed_name_at_house6 = 'Carol'
    fixed_music_at_house3 = 'hip hop'
    fixed_music_at_house6 = 'country'

    solutions = []

    # Prepare name permutations with Carol fixed at house 6
    other_names = [n for n in names if n != fixed_name_at_house6]
    for name_perm in permutations(other_names):
        names_by_house = list(name_perm) + [fixed_name_at_house6]  # indices 0..5 for houses 1..6
        pos_name = {n: i + 1 for i, n in enumerate(names_by_house)}

        # Apply name-only constraints early:
        # Clue 6: Arnold is not in the fifth house.
        if pos_name['Arnold'] == 5:
            continue

        # Clue 2 and 4 with Clue 9 together imply Eric must be at house 2 (left and adjacent to house 3 hip hop)
        if pos_name['Eric'] != 2:
            continue

        # Clue 10: There is one house between Peter and Bob.
        if abs(pos_name['Peter'] - pos_name['Bob']) != 2:
            continue

        # Clue 7: Arnold is somewhere to the right of the person who loves pop music.
        # Since pop is Peter's favorite (clue 8), Arnold is to the right of Peter.
        if not (pos_name['Arnold'] > pos_name['Peter']):
            continue

        # Now assign music with fixed positions for hip hop and country
        other_musics = [m for m in musics if m not in (fixed_music_at_house3, fixed_music_at_house6)]
        music_positions = [0, 1, 3, 4]  # Houses 1,2,4,5 (0-based indices)

        for music_perm in permutations(other_musics):
            musics_by_house = [None] * 6
            musics_by_house[2] = fixed_music_at_house3  # house 3
            musics_by_house[5] = fixed_music_at_house6  # house 6

            for idx, pos in enumerate(music_positions):
                musics_by_house[pos] = music_perm[idx]

            # Clue 11: The person who loves rock music is not in the fifth house.
            if musics_by_house[4] == 'rock':
                continue

            # Clue 8: The person who loves pop music is Peter.
            # So at Peter's house, music must be pop.
            if musics_by_house[pos_name['Peter'] - 1] != 'pop':
                continue

            # Clue 1: Bob is directly left of the person who loves jazz music.
            bob_index = pos_name['Bob'] - 1
            if not (0 <= bob_index < 5 and musics_by_house[bob_index + 1] == 'jazz'):
                continue

            # Clue 2: Eric is somewhere to the left of the person who loves hip hop.
            # Clue 4: Eric and the person who loves hip hop are next to each other.
            hiphop_house = 3
            if not (pos_name['Eric'] < hiphop_house and abs(pos_name['Eric'] - hiphop_house) == 1):
                continue

            # All constraints satisfied
            solutions.append((names_by_house, musics_by_house))

    # Select the first solution (expected unique)
    if not solutions:
        raise RuntimeError("No solution found.")
    names_by_house, musics_by_house = solutions[0]

    # Build JSON output
    header = ["House", "Name", "MusicGenre"]
    rows = []
    for i in range(6):
        house_num = str(i + 1)
        rows.append([house_num, names_by_house[i], musics_by_house[i]])

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))