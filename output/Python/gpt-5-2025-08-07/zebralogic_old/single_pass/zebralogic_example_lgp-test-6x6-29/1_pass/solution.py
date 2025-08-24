import itertools
import json

def solve():
    houses = [1, 2, 3, 4, 5, 6]

    Names = ['Arnold', 'Carol', 'Peter', 'Eric', 'Bob', 'Alice']
    Styles = ['ranch', 'colonial', 'modern', 'craftsman', 'mediterranean', 'victorian']
    Foods = ['pizza', 'stew', 'spaghetti', 'grilled cheese', 'stir fry', 'soup']
    Vacations = ['cultural', 'cruise', 'mountain', 'camping', 'city', 'beach']
    Heights = ['average', 'very tall', 'very short', 'short', 'tall', 'super tall']
    Cigars = ['yellow monster', 'prince', 'dunhill', 'pall mall', 'blue master', 'blends']

    # Helper to get positions of items in a list
    def pos_of(mapping_list):
        return {v: i for i, v in enumerate(mapping_list)}

    solutions = []

    # Names: Apply constraints 1 (Alice at 5 -> index 4), 9 (Eric at 4 -> index 3)
    # We'll permute remaining names in remaining positions and apply name-only implications from other rules.
    fixed_names = [None] * 6
    fixed_names[4] = 'Alice'  # clue 1
    fixed_names[3] = 'Eric'   # clue 9
    remaining_positions = [i for i in range(6) if fixed_names[i] is None]  # [0,1,2,5]
    remaining_names = [n for n in Names if n not in fixed_names]           # ['Arnold','Carol','Peter','Bob']

    for perm_names in itertools.permutations(remaining_names):
        names = fixed_names[:]
        for idx, p in zip(remaining_positions, perm_names):
            names[idx] = p

        name_pos = pos_of(names)
        # Clue 17: stir fry directly left of Bob -> Bob not in house 1 (index 0)
        if name_pos['Bob'] == 0:
            continue

        # Clues 7 and 17 and 5 combined:
        # average = stir fry; stir fry directly left of Bob -> pos_avg = pos_Bob - 1
        # There is one house between average and Peter -> |pos_avg - pos_Peter| = 2
        pos_bob = name_pos['Bob']
        pos_avg = pos_bob - 1
        if not (0 <= pos_avg <= 5):
            continue
        # |pos_avg - pos_peter| == 2
        if abs(pos_avg - name_pos['Peter']) != 2:
            continue

        # Clue 3 interpreted as "Alice is the spaghetti eater": Food at Alice's house is spaghetti.
        # We'll use this later in foods.

        # Clue 4: Arnold loves stew: Food at Arnold's house will be stew (later check).

        # Proceed to Foods
        # Fixed: food at pos_avg is stir fry (from 7); food at Alice (index 4) is spaghetti (3);
        # food at Arnold (name_pos['Arnold']) is stew (4).
        food = [None] * 6
        food[pos_avg] = 'stir fry'                 # clues 2 & 7 link later to colonial
        food[4] = 'spaghetti'                      # clue 3
        food[name_pos['Arnold']] = 'stew'          # clue 4

        remaining_foods = [f for f in Foods if f not in food]
        remaining_positions_food = [i for i in range(6) if food[i] is None]

        for perm_foods in itertools.permutations(remaining_foods):
            foods = food[:]
            for idx, f in zip(remaining_positions_food, perm_foods):
                foods[idx] = f

            food_pos = pos_of(foods)

            # Clue 17 already used (stir fry = left of Bob ensured via names and pos_avg)

            # Next, House Styles
            style = [None] * 6
            # Clue 2: stir fry person is colonial
            style[pos_avg] = 'colonial'
            # Clue 14 (and 3 interpretation): spaghetti eater resides in Victorian -> Alice's house is Victorian
            style[4] = 'victorian'

            remaining_styles = [s for s in Styles if s not in style]
            remaining_positions_style = [i for i in range(6) if style[i] is None]

            # Constraint: Clue 6: Craftsman not in third house (index 2)
            # Constraint: Clue 18: modern somewhere to the left of Alice (index 4) -> modern index < 4
            for perm_styles in itertools.permutations(remaining_styles):
                styles = style[:]
                valid_styles = True
                for idx, st in zip(remaining_positions_style, perm_styles):
                    # skip assignments that violate craftsman != house 3 now
                    if idx == 2 and st == 'craftsman':
                        valid_styles = False
                        break
                    styles[idx] = st
                if not valid_styles:
                    continue

                style_pos = pos_of(styles)
                # Check modern left of Alice
                if style_pos['modern'] >= 4:
                    continue

                # Now Heights
                height = [None] * 6
                # Clue 7: average = stir fry -> pos_avg already
                height[pos_avg] = 'average'

                remaining_heights = [h for h in Heights if h not in height]
                remaining_positions_height = [i for i in range(6) if height[i] is None]

                for perm_heights in itertools.permutations(remaining_heights):
                    heights = height[:]
                    for idx, h in zip(remaining_positions_height, perm_heights):
                        heights[idx] = h

                    height_pos = pos_of(heights)

                    # Clue 5: one house between average and Peter (already ensured via names-stage derivation),
                    # but verify consistency with current heights
                    if abs(height_pos['average'] - name_pos['Peter']) != 2:
                        continue

                    # Clue 16: tall left of Victorian
                    if not (height_pos['tall'] < style_pos['victorian']):
                        continue

                    # Clue 21: two houses between grilled cheese and super tall
                    if abs(food_pos['grilled cheese'] - height_pos['super tall']) != 3:
                        continue

                    # Clue 19: Craftsman left of short
                    if not (style_pos['craftsman'] < height_pos['short']):
                        continue

                    # Now Vacations
                    vacation = [None] * 6

                    # Clue 10: one house between colonial and camping
                    # pos_colonial is pos_avg; so camping at pos_avg + 2 or pos_avg - 2
                    possible_camping_positions = []
                    if 0 <= pos_avg + 2 <= 5:
                        possible_camping_positions.append(pos_avg + 2)
                    if 0 <= pos_avg - 2 <= 5:
                        possible_camping_positions.append(pos_avg - 2)
                    # Set camping if uniquely determined by colonial at pos_avg
                    # Actually both could be possible; but we can set constraints after permutation.
                    # To reduce branching, we can enforce by early check:
                    # We'll encode via constraint check later in loop after assignment.

                    remaining_vacations = Vacations[:]
                    # We'll generate permutations but enforce the many equalities:

                    # To reduce permutations, pre-assign what we can:
                    # Clue 12: very tall = mountain
                    pos_mountain = height_pos['very tall']
                    # Clue 11 already ties to Yellow Monster; applied in cigars stage

                    # Clue 8: beach = ranch
                    pos_beach = style_pos['ranch']

                    # Clue 15: tall = beach -> positions equal, consistency check
                    if height_pos['tall'] != pos_beach:
                        continue

                    # We'll now construct vacation list with some fixed positions:
                    vac_fixed = [None] * 6
                    vac_fixed[pos_beach] = 'beach'
                    vac_fixed[pos_mountain] = 'mountain'
                    # Clue 10: camping position(s)
                    # Because colonial is pos_avg, camping must be pos_avg +/- 2.
                    # If both positions are free, we'll let permutation fill but ensure later.
                    # But we can optionally try both possibilities explicitly to reduce perms.
                    for camp_pos in possible_camping_positions:
                        vac_fixed2 = vac_fixed[:]
                        vac_fixed2[camp_pos] = 'camping'

                        # Clue 24: cultural = pizza
                        pos_pizza = food_pos['pizza']
                        vac_fixed2[pos_pizza] = 'cultural'

                        # Prepare remaining vacations to place
                        used_vacs = [v for v in vac_fixed2 if v is not None]
                        vac_remaining_items = [v for v in Vacations if v not in used_vacs]
                        vac_remaining_positions = [i for i in range(6) if vac_fixed2[i] is None]

                        for perm_vacs in itertools.permutations(vac_remaining_items):
                            vacations = vac_fixed2[:]
                            for idx, v in zip(vac_remaining_positions, perm_vacs):
                                vacations[idx] = v

                            vac_pos = pos_of(vacations)

                            # Validate camping distance from colonial (pos_avg)
                            if abs(vac_pos['camping'] - pos_avg) != 2:
                                continue

                            # Clue 25: pizza left of cruise
                            if not (pos_pizza < vac_pos['cruise']):
                                continue

                            # Now Cigars
                            cigar = [None] * 6

                            # Clue 22: ranch = Blue Master
                            pos_ranch = style_pos['ranch']
                            cigar[pos_ranch] = 'blue master'
                            # Clue 23: blends directly left of Blue Master
                            if pos_ranch - 1 < 0:
                                continue
                            cigar[pos_ranch - 1] = 'blends'

                            # Clue 11: mountain = Yellow Monster
                            pos_mountain = vac_pos['mountain']
                            if cigar[pos_mountain] is not None and cigar[pos_mountain] != 'yellow monster':
                                continue
                            cigar[pos_mountain] = 'yellow monster'

                            # Clue 13: mountain adjacent to Dunhill
                            # So Dunhill must be at one of the adjacent positions.
                            adj_positions = []
                            if pos_mountain - 1 >= 0:
                                adj_positions.append(pos_mountain - 1)
                            if pos_mountain + 1 <= 5:
                                adj_positions.append(pos_mountain + 1)

                            # Prepare remaining cigars to place
                            used_cigars = [c for c in cigar if c is not None]
                            cigar_remaining_items = [c for c in Cigars if c not in used_cigars]
                            cigar_remaining_positions = [i for i in range(6) if cigar[i] is None]

                            for perm_cigars in itertools.permutations(cigar_remaining_items):
                                cigars = cigar[:]
                                for idx, c in zip(cigar_remaining_positions, perm_cigars):
                                    cigars[idx] = c

                                cigar_pos = pos_of(cigars)

                                # Enforce adjacency of Dunhill to Mountain (clue 13)
                                if cigar_pos['dunhill'] not in adj_positions:
                                    continue

                                # Clue 20: stir fry left of Prince
                                if not (pos_avg < cigar_pos['prince']):
                                    continue

                                # All constraints satisfied if we reach here
                                # Build solution rows from house 1..6 (index 0..5)
                                rows = []
                                for i in range(6):
                                    rows.append([
                                        str(i + 1),
                                        names[i],
                                        styles[i],
                                        foods[i],
                                        vacations[i],
                                        heights[i],
                                        cigars[i]
                                    ])
                                solutions.append({
                                    "header": ["House", "Name", "HouseStyle", "Food", "Vacation", "Height", "Cigar"],
                                    "rows": rows
                                })
                                # Assuming unique solution; but we can break after first
                                return {"solution": solutions[0]}

    return None

result = solve()
print(json.dumps({"solution": result["solution"]}, ensure_ascii=False, indent=2))