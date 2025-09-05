import json

def solve():
    houses = [1, 2, 3, 4, 5, 6]

    Names = ["Eric", "Alice", "Arnold", "Carol", "Peter", "Bob"]
    Styles = ["mediterranean", "modern", "craftsman", "ranch", "colonial", "victorian"]
    Music = ["country", "hip hop", "pop", "jazz", "classical", "rock"]
    Hobbies = ["cooking", "painting", "photography", "woodworking", "gardening", "knitting"]

    # Helper to invert mapping value->pos into pos->value
    def invert_map(m):
        inv = {}
        for k, v in m.items():
            inv[v] = k
        return inv

    # Try all viable name placements first (highly constrained)
    # Fixed: Bob at 3
    # From clue 5 and 1: only Eric at 4 or 5 works (jazz directly left of Eric, rock at 5, country at 1)
    # Carol cannot be at 1,5,6 because those houses have fixed music incompatible with hip hop at Carol's house
    # and 6 cannot be left of knitting.
    for eric_pos in [4, 5]:
        name_pos = {}
        name_pos["Bob"] = 3
        name_pos["Eric"] = eric_pos

        # Determine allowable positions for Carol
        possible_carol_positions = [p for p in houses if p not in {name_pos["Bob"], name_pos["Eric"]} and p not in {1, 5, 6}]
        # Also if Eric is at 5 then house 4 is jazz (so Carol can't be at 4 because Carol must be hip hop)
        # If Eric is at 4 then Carol can't be at 4 anyway because Eric is there.
        # This simplifies to Carol must be at 2 in all valid cases.
        for carol_pos in possible_carol_positions:
            name_pos["Carol"] = carol_pos

            remaining = [p for p in houses if p not in set(name_pos.values())]
            # Choose Arnold
            for arnold_pos in remaining:
                name_pos["Arnold"] = arnold_pos
                remaining2 = [p for p in remaining if p != arnold_pos]
                # Choose Alice
                for alice_pos in remaining2:
                    name_pos["Alice"] = alice_pos
                    remaining3 = [p for p in remaining2 if p != alice_pos]
                    # Peter is the last remaining
                    if len(remaining3) != 1:
                        continue
                    name_pos["Peter"] = remaining3[0]

                    # With names fixed, assign music based on clues:
                    music_pos = {}
                    music_pos["rock"] = 5                 # Clue 1
                    music_pos["country"] = 1              # Clue 11
                    # Clue 5: jazz directly left of Eric
                    music_pos["jazz"] = name_pos["Eric"] - 1
                    # Quick viability check:
                    if music_pos["jazz"] < 1 or music_pos["jazz"] > 6:
                        continue
                    # Clue 7 + 3: Carol loves hip hop and that house is Mediterranean
                    music_pos["hip hop"] = name_pos["Carol"]

                    # Ensure no duplicate houses among already assigned music
                    if len(set(music_pos.values())) != len(music_pos):
                        continue

                    # Assign styles based on clues
                    style_pos = {}
                    style_pos["ranch"] = name_pos["Eric"]             # Clue 9
                    style_pos["craftsman"] = name_pos["Arnold"]       # Clue 8
                    style_pos["mediterranean"] = music_pos["hip hop"] # Clue 3
                    # Victorian unknown yet (but constrained by Arnold ±3)
                    # Clue 4: two houses between Arnold and Victorian
                    victorian_candidates = []
                    for delta in (-3, 3):
                        vpos = name_pos["Arnold"] + delta
                        if 1 <= vpos <= 6:
                            # Cannot coincide with already assigned distinct styles
                            if vpos in {style_pos["ranch"], style_pos["craftsman"], style_pos["mediterranean"]}:
                                continue
                            victorian_candidates.append(vpos)

                    # Assign remaining music "classical" (adjacent to Victorian/woodworking), and "pop" leftover
                    for vpos in victorian_candidates:
                        # Clue 10: Woodworking = Victorian (hobby later)
                        # Clue 2: Classical next to Woodworking/Victorian
                        neighbors = [x for x in [vpos - 1, vpos + 1] if 1 <= x <= 6]
                        # Classical must be in neighbors and not already taken by other fixed music
                        taken_music_positions = set(music_pos.values())
                        classical_candidates = [n for n in neighbors if n not in taken_music_positions]
                        # Additionally, house 5 is rock, so classical cannot be at 5
                        classical_candidates = [n for n in classical_candidates if n != 5]
                        # Also house 1 is country, so classical cannot be at 1
                        classical_candidates = [n for n in classical_candidates if n != 1]
                        if not classical_candidates:
                            continue

                        # Try each possible classical position
                        for cpos in classical_candidates:
                            music_pos2 = dict(music_pos)
                            music_pos2["classical"] = cpos
                            # The remaining music is pop
                            remaining_music_positions = [p for p in houses if p not in set(music_pos2.values())]
                            if len(remaining_music_positions) != 1:
                                continue
                            music_pos2["pop"] = remaining_music_positions[0]

                            # Now fix the chosen Victorian
                            style_pos2 = dict(style_pos)
                            style_pos2["victorian"] = vpos

                            # Ensure style uniqueness so far
                            if len(set(style_pos2.values())) != len(style_pos2):
                                continue

                            # Hobbies based on clues
                            hobby_pos = {}
                            hobby_pos["gardening"] = name_pos["Eric"]         # Clue 14
                            hobby_pos["photography"] = name_pos["Alice"]      # Clue 13
                            hobby_pos["woodworking"] = style_pos2["victorian"]# Clue 10

                            # Clue 2: already enforced via classical next to Victorian

                            # Clue 6: Hip hop left of knitting
                            # Choose knitting position to the right of Carol and not conflicting with assigned hobbies
                            occupied_hobby_positions = set(hobby_pos.values())
                            knitting_candidates = [p for p in houses if p > name_pos["Carol"] and p not in occupied_hobby_positions]
                            if not knitting_candidates:
                                continue

                            for knit_pos in knitting_candidates:
                                hobby_pos2 = dict(hobby_pos)
                                hobby_pos2["knitting"] = knit_pos

                                # Now assign styles "colonial" and "modern"
                                assigned_style_positions = set(style_pos2.values())
                                # Colonial and modern must occupy the remaining two houses
                                remaining_style_positions = [p for p in houses if p not in assigned_style_positions]
                                if len(remaining_style_positions) != 2:
                                    continue

                                # Try both choices for colonial; modern will be the other
                                for colonial_pos in remaining_style_positions:
                                    style_pos3 = dict(style_pos2)
                                    style_pos3["colonial"] = colonial_pos
                                    modern_pos = [p for p in remaining_style_positions if p != colonial_pos][0]
                                    style_pos3["modern"] = modern_pos

                                    # Clue 12: One house between painter and colonial
                                    # Choose painting among remaining hobby slots that fits this rule
                                    occupied_hobby_positions2 = set(hobby_pos2.values())
                                    # Available houses for remaining hobbies (painting, cooking)
                                    free_hobby_positions = [p for p in houses if p not in occupied_hobby_positions2]
                                    # Painting must be exactly 2 away from colonial
                                    painting_candidates = [p for p in free_hobby_positions if abs(p - style_pos3["colonial"]) == 2]
                                    if not painting_candidates:
                                        continue

                                    for paint_pos in painting_candidates:
                                        hobby_pos3 = dict(hobby_pos2)
                                        hobby_pos3["painting"] = paint_pos
                                        # Remaining hobby is cooking
                                        remaining_hobby_positions = [p for p in houses if p not in set(hobby_pos3.values())]
                                        if len(remaining_hobby_positions) != 1:
                                            continue
                                        hobby_pos3["cooking"] = remaining_hobby_positions[0]

                                        # Validate all uniqueness and constraints
                                        # 1) All categories cover all houses uniquely
                                        if len(set(name_pos.values())) != 6:
                                            continue
                                        if len(set(style_pos3.values())) != 6:
                                            continue
                                        if len(set(music_pos2.values())) != 6:
                                            continue
                                        if len(set(hobby_pos3.values())) != 6:
                                            continue

                                        # Clue 5 already enforced by construction; just sanity check
                                        if not (music_pos2["jazz"] + 1 == name_pos["Eric"]):
                                            continue
                                        # Clue 6 hip hop to the left of knitting
                                        if not (music_pos2["hip hop"] < hobby_pos3["knitting"]):
                                            continue
                                        # Clue 3 mediterranean = hip hop
                                        if not (style_pos3["mediterranean"] == music_pos2["hip hop"]):
                                            continue
                                        # Clue 4 Arnold and Victorian distance 3
                                        if not (abs(name_pos["Arnold"] - style_pos3["victorian"]) == 3):
                                            continue
                                        # Clue 2 classical next to woodworking
                                        if not (abs(music_pos2["classical"] - hobby_pos3["woodworking"]) == 1):
                                            continue
                                        # Clue 8 Arnold = craftsman
                                        if not (style_pos3["craftsman"] == name_pos["Arnold"]):
                                            continue
                                        # Clue 9 Ranch = Eric
                                        if not (style_pos3["ranch"] == name_pos["Eric"]):
                                            continue
                                        # Clue 10 Woodworking = Victorian
                                        if not (hobby_pos3["woodworking"] == style_pos3["victorian"]):
                                            continue
                                        # Clue 11 country in 1
                                        if not (music_pos2["country"] == 1):
                                            continue
                                        # Clue 12 Painting one house between Colonial
                                        if not (abs(hobby_pos3["painting"] - style_pos3["colonial"]) == 2):
                                            continue
                                        # Clue 13 Alice photography
                                        if not (hobby_pos3["photography"] == name_pos["Alice"]):
                                            continue
                                        # Clue 14 Gardening = Eric
                                        if not (hobby_pos3["gardening"] == name_pos["Eric"]):
                                            continue
                                        # Clue 15 Bob in 3
                                        if not (name_pos["Bob"] == 3):
                                            continue
                                        # Clue 1 Rock in 5
                                        if not (music_pos2["rock"] == 5):
                                            continue
                                        # Ensure Carol hip-hop
                                        if not (music_pos2["hip hop"] == name_pos["Carol"]):
                                            continue

                                        # If we reached here, we found a valid solution
                                        # Build final house mapping
                                        name_at = invert_map(name_pos)
                                        style_at = invert_map(style_pos3)
                                        music_at = invert_map(music_pos2)
                                        hobby_at = invert_map(hobby_pos3)

                                        rows = []
                                        for h in houses:
                                            rows.append([
                                                str(h),
                                                name_at[h],
                                                style_at[h],
                                                music_at[h],
                                                hobby_at[h]
                                            ])
                                        return {
                                            "solution": {
                                                "header": ["House", "Name", "HouseStyle", "MusicGenre", "Hobby"],
                                                "rows": rows
                                            }
                                        }
    return None

def main():
    result = solve()
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()