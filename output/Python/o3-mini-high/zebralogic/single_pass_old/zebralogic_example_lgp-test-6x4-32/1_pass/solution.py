#!/usr/bin/env python3
import itertools
import json

def main():
    # Define the lists for each attribute.
    names = ["Eric", "Alice", "Arnold", "Carol", "Peter", "Bob"]
    styles = ["mediterranean", "modern", "craftsman", "ranch", "colonial", "victorian"]
    music = ["country", "hip hop", "pop", "jazz", "classical", "rock"]
    hobbies = ["cooking", "painting", "photography", "woodworking", "gardening", "knitting"]

    # We'll use 0-indexed houses (house 1 -> index0, house 6 -> index5)
    for name_perm in itertools.permutations(names):
        # Clue 15: Bob is in the third house (house index 2)
        if name_perm[2] != "Bob":
            continue

        # Iterate over house styles permutations.
        for style_perm in itertools.permutations(styles):
            valid = True
            # Clue 8: The person in a Craftsman-style house is Arnold.
            # Clue 9: The person in a ranch-style home is Eric.
            for i in range(6):
                if name_perm[i] == "Arnold" and style_perm[i] != "craftsman":
                    valid = False
                    break
                if name_perm[i] == "Eric" and style_perm[i] != "ranch":
                    valid = False
                    break
            if not valid:
                continue

            # Iterate over music permutations.
            for music_perm in itertools.permutations(music):
                # Clue 11: The person who loves country music is in the first house.
                if music_perm[0] != "country":
                    continue
                # Clue 1: The person who loves rock music is in the fifth house.
                if music_perm[4] != "rock":
                    continue

                # Clue 3: The person in a Mediterranean-style villa is the person who loves hip-hop music.
                # So for each house, if style is mediterranean, music must be hip hop and vice versa.
                valid_music = True
                for i in range(6):
                    if style_perm[i] == "mediterranean" and music_perm[i] != "hip hop":
                        valid_music = False
                        break
                    if music_perm[i] == "hip hop" and style_perm[i] != "mediterranean":
                        valid_music = False
                        break
                if not valid_music:
                    continue

                # Clue 5: The person who loves jazz music is directly left of Eric.
                try:
                    idx_eric = name_perm.index("Eric")
                except ValueError:
                    continue
                if idx_eric == 0 or music_perm[idx_eric - 1] != "jazz":
                    continue

                # Iterate over hobbies permutations.
                for hobby_perm in itertools.permutations(hobbies):
                    valid_hobby = True
                    for i in range(6):
                        # Clue 13: Alice is the photography enthusiast.
                        if name_perm[i] == "Alice" and hobby_perm[i] != "photography":
                            valid_hobby = False
                            break
                        # Clue 14: Eric enjoys gardening.
                        if name_perm[i] == "Eric" and hobby_perm[i] != "gardening":
                            valid_hobby = False
                            break
                        # Clue 10: The woodworking hobbyist is the person residing in a Victorian house.
                        # Enforce bidirectional link: if hobby is woodworking, style must be victorian, and vice versa.
                        if style_perm[i] == "victorian" and hobby_perm[i] != "woodworking":
                            valid_hobby = False
                            break
                        if hobby_perm[i] == "woodworking" and style_perm[i] != "victorian":
                            valid_hobby = False
                            break
                    if not valid_hobby:
                        continue

                    # Clue 12: There is one house between the person who paints as a hobby and the person living in a colonial-style house.
                    try:
                        index_paint = hobby_perm.index("painting")
                        index_colonial = style_perm.index("colonial")
                    except ValueError:
                        continue
                    if abs(index_paint - index_colonial) != 2:
                        continue

                    # Clue 2: The person who loves classical music and the woodworking hobbyist are next to each other.
                    # Find the index of the house with classical music.
                    try:
                        index_classical = music_perm.index("classical")
                    except ValueError:
                        continue
                    left_neighbor = music_perm[index_classical - 1] if index_classical - 1 >= 0 else None
                    right_neighbor = music_perm[index_classical + 1] if index_classical + 1 < 6 else None
                    # Instead of checking music, we check hobby for woodworking because of the link.
                    neighbor_ok = False
                    if index_classical - 1 >= 0 and hobby_perm[index_classical - 1] == "woodworking":
                        neighbor_ok = True
                    if index_classical + 1 < 6 and hobby_perm[index_classical + 1] == "woodworking":
                        neighbor_ok = True
                    if not neighbor_ok:
                        continue

                    # Clue 6: The person who loves hip hop music is somewhere to the left of the person who enjoys knitting.
                    # Also, by Clue 7 Carol is the person who loves hip hop.
                    # Enforce that for every house: if the person is Carol, then music must be hip hop.
                    for i in range(6):
                        if name_perm[i] == "Carol" and music_perm[i] != "hip hop":
                            valid_hobby = False
                            break
                    if not valid_hobby:
                        continue
                    try:
                        index_hiphop = music_perm.index("hip hop")  # should correspond to Carol
                        index_knitting = hobby_perm.index("knitting")
                    except ValueError:
                        continue
                    if not (index_hiphop < index_knitting):
                        continue

                    # Clue 4: There are two houses between Arnold and the person residing in a Victorian house.
                    try:
                        index_arnold = name_perm.index("Arnold")
                        index_victorian = style_perm.index("victorian")
                    except ValueError:
                        continue
                    if abs(index_arnold - index_victorian) != 3:
                        continue

                    # All constraints have been satisfied.
                    # Build the solution as a list of rows, one for each house: House#, Name, House Style, Favorite Music Genre, Hobby.
                    solution_rows = []
                    for i in range(6):
                        # House numbers are 1-indexed in output.
                        solution_rows.append([
                            str(i + 1),
                            name_perm[i],
                            style_perm[i],
                            music_perm[i],
                            hobby_perm[i]
                        ])

                    result = {
                        "solution": {
                            "header": ["House", "Name", "House Style", "Favorite Music Genre", "Hobby"],
                            "rows": solution_rows
                        }
                    }
                    print(json.dumps(result, indent=2))
                    return

if __name__ == '__main__':
    main()