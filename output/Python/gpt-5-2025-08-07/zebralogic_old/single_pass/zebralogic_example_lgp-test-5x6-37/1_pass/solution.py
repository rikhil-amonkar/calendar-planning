import json
import itertools

def solve():
    houses = [0,1,2,3,4]  # indices for houses 1..5

    Names = ['Bob', 'Arnold', 'Alice', 'Peter', 'Eric']
    Hobbies = ['cooking', 'gardening', 'painting', 'photography', 'knitting']
    Sports = ['swimming', 'tennis', 'soccer', 'baseball', 'basketball']
    Styles = ['ranch', 'craftsman', 'victorian', 'modern', 'colonial']
    Children = ['Timothy', 'Samantha', 'Bella', 'Meredith', 'Fred']
    Heights = ['average', 'very tall', 'very short', 'short', 'tall']

    # Helper to check neighbor
    def is_next_to(i, j):
        return abs(i - j) == 1

    solution = None

    # Enumerate names - fix Alice at house 2 (index 1) and Peter at house 4 (index 3)
    for name_perm in itertools.permutations(Names):
        name_by_house = list(name_perm)
        if name_by_house[1] != 'Alice':
            continue
        if name_by_house[3] != 'Peter':
            continue

        # Clue 3: Peter is directly left of the person residing in a Victorian house (house index 4 must be Victorian later)
        # This will be enforced when assigning styles along with clue 20 (Victorian at house 5).

        # Hobbies partial constraints now:
        # Clue 8: gardening is in the second house (index 1)
        # Clue 7: Bob paints
        # Clue 18: knitting is next to gardening (i.e., index 0 or 2)
        # Clue 19: modern is cooking (handled in styles/hobbies step)
        # We'll enforce during hobby/style assignment

        # Enumerate styles - fix Victorian at house 5 (index 4)
        for style_perm in itertools.permutations(Styles):
            style_by_house = list(style_perm)
            if style_by_house[4] != 'victorian':
                continue

            # Clue 3 again: Peter directly left of Victorian -> house 3 (index 3) must be Peter (already true)
            if name_by_house[3] != 'Peter':
                continue

            # Clue 19 + 12 + 10 implications will tie to modern later. But we can prune:
            # Modern cannot be index 4 (Victorian), cannot be index 1 (since house 2's hobby is gardening, modern implies cooking),
            # cannot be index 3 (house 4 has baseball/very tall per other clues -> modern implies tennis conflict).
            modern_idx = style_by_house.index('modern')
            if modern_idx in (1, 3, 4):
                continue

            # Clue 17: ranch left of cooking; with 19 cooking=modern -> ranch left of modern
            ranch_idx = style_by_house.index('ranch')
            if not (ranch_idx < modern_idx):
                continue

            # Additional pruning using height constraints later:
            # Clue 13: Craftsman-style house has average height; Clue 2 and 16 fix heights at indices 1 and 3 respectively
            craftsman_idx = style_by_house.index('craftsman')
            # If craftsman at index 1 or 3 it's impossible because those heights are fixed to tall and very tall, not average.
            if craftsman_idx in (1, 3):
                continue

            # Children assignment:
            # Clue 14: child Fred resides in Victorian (index 4)
            # Clue 12: Samantha is in modern-style house
            # Clue 1: average height person has child Meredith, and by Clue 13 average height is in Craftsman house
            children_by_house = [None]*5
            children_by_house[4] = 'Fred'  # Clue 14
            children_by_house[modern_idx] = 'Samantha'  # Clue 12 (and implies tennis later)
            children_by_house[craftsman_idx] = 'Meredith'  # Clue 1 + 13

            remaining_children = [c for c in Children if c not in children_by_house]
            remaining_positions = [i for i in houses if children_by_house[i] is None]
            # There should be exactly two remaining children and positions
            for extra_children in itertools.permutations(remaining_children):
                children_test = children_by_house[:]
                valid_children = True
                for pos, child in zip(remaining_positions, extra_children):
                    children_test[pos] = child

                # Clue 6: Meredith and Timothy are next to each other
                m_idx = children_test.index('Meredith')
                t_idx = children_test.index('Timothy')
                if not is_next_to(m_idx, t_idx):
                    valid_children = False

                if not valid_children:
                    continue

                # Heights assignment:
                height_by_house = [None]*5
                # Clue 2: tall in house 2 (index 1)
                height_by_house[1] = 'tall'
                # Clue 16: Peter is very tall -> index of Peter
                height_by_house[3] = 'very tall'
                # Clue 13 and 1: Craftsman -> average -> child Meredith already set
                height_by_house[craftsman_idx] = 'average'

                # Remaining heights to assign
                rem_heights = [h for h in Heights if h not in height_by_house]
                rem_positions = [i for i in houses if height_by_house[i] is None]

                # Enumerate possible assignments for remaining heights
                for extra_heights in itertools.permutations(rem_heights):
                    heights_test = height_by_house[:]
                    for pos, ht in zip(rem_positions, extra_heights):
                        heights_test[pos] = ht

                    # Clue 9: very short is somewhere to the right of Eric
                    eric_idx = name_by_house.index('Eric')
                    vs_idx = heights_test.index('very short')
                    if not (vs_idx > eric_idx):
                        continue

                    # Hobbies assignment:
                    hobby_by_house = [None]*5
                    # Clue 8: gardening at index 1
                    hobby_by_house[1] = 'gardening'
                    # Clue 19: modern -> cooking
                    hobby_by_house[modern_idx] = 'cooking'
                    # Clue 7: Bob paints
                    bob_idx = name_by_house.index('Bob')
                    # If Bob is at the same house as gardening or cooking, painting would conflict; we will enforce uniqueness below.
                    # For now, set Bob's hobby.
                    # If conflict arises (same index already assigned), skip.
                    if hobby_by_house[bob_idx] is not None and hobby_by_house[bob_idx] != 'painting':
                        continue
                    hobby_by_house[bob_idx] = 'painting'

                    # Clue 18: knitting next to gardening (index 1), so knitting must be at index 0 or 2
                    # But if modern_idx == 2, cooking at 2, knitting can't be 2; we'll check when assigning.
                    remaining_hobbies = [h for h in Hobbies if h not in hobby_by_house]
                    remaining_positions_hobby = [i for i in houses if hobby_by_house[i] is None]

                    for extra_hobbies in itertools.permutations(remaining_hobbies):
                        hb_test = hobby_by_house[:]
                        consistent = True
                        for pos, hb in zip(remaining_positions_hobby, extra_hobbies):
                            # enforce knitting adjacency when assigning
                            hb_test[pos] = hb

                        # Check knitting next to gardening at index 1
                        knit_idx = hb_test.index('knitting') if 'knitting' in hb_test else None
                        if knit_idx is None or not is_next_to(knit_idx, 1):
                            consistent = False

                        # Ensure unique assignments satisfied (they are by permutation)
                        if not consistent:
                            continue

                        # Sports assignment:
                        sport_by_house = [None]*5
                        # Clue 5: baseball is very tall (and Peter per 16), ensure house 4 (index 3) has baseball
                        sport_by_house[3] = 'baseball'
                        # Clue 10: tennis with Samantha; Samantha is at modern_idx
                        sport_by_house[modern_idx] = 'tennis'
                        # Clue 15: short -> basketball
                        short_idx = heights_test.index('short')
                        sport_by_house[short_idx] = 'basketball'
                        # Clue 11: soccer not in first house (index 0), we'll check after assignment.

                        remaining_sports = [s for s in Sports if s not in sport_by_house]
                        remaining_positions_sport = [i for i in houses if sport_by_house[i] is None]

                        for extra_sports in itertools.permutations(remaining_sports):
                            sp_test = sport_by_house[:]
                            for pos, sp in zip(remaining_positions_sport, extra_sports):
                                sp_test[pos] = sp

                            # Clue 11: soccer not in the first house (index 0)
                            if sp_test[0] == 'soccer':
                                continue

                            # All constraints satisfied
                            solution = {
                                "names": name_by_house,
                                "hobbies": hb_test,
                                "sports": sp_test,
                                "styles": style_by_house,
                                "children": children_test,
                                "heights": heights_test
                            }
                            return solution
    return None

res = solve()

# Prepare output JSON structure
output = {
    "solution": {
        "header": ["House", "Name", "Hobby", "FavoriteSport", "HouseStyle", "Children", "Height"],
        "rows": []
    }
}

if res:
    for i in range(5):
        row = [
            str(i+1),
            res["names"][i],
            res["hobbies"][i],
            res["sports"][i],
            res["styles"][i],
            res["children"][i],
            res["heights"][i]
        ]
        output["solution"]["rows"].append(row)

print(json.dumps(output, indent=2))