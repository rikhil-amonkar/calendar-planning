import json
import itertools

def solve_puzzle():
    houses = list(range(5))  # 0..4 for houses 1..5

    Names = ['Alice', 'Peter', 'Bob', 'Eric', 'Arnold']
    Heights = ['very short', 'short', 'tall', 'average', 'very tall']
    Mothers = ['Janelle', 'Kailyn', 'Penny', 'Holly', 'Aniya']
    Hairs = ['blonde', 'black', 'gray', 'red', 'brown']

    solutions = []

    # Iterate over all mother placements with house 3 (index 2) = Kailyn
    for mothers_perm in itertools.permutations(Mothers):
        if mothers_perm[2] != 'Kailyn':
            continue

        pos_mother = {m: i for i, m in enumerate(mothers_perm)}

        # Clue 10 + 14: Kailyn is in the third house and directly left of the person who is short.
        pos_short = pos_mother['Kailyn'] + 1
        if pos_short < 0 or pos_short > 4:
            continue
        if pos_short != 3:  # Must be house 4
            continue

        # Clue 2: average and short are 3 apart
        possible_avg_positions = []
        for delta in (-3, 3):
            p = pos_short + delta
            if 0 <= p <= 4:
                possible_avg_positions.append(p)
        # There should be exactly one valid position (0) given pos_short=3
        if len(possible_avg_positions) == 0:
            continue
        # Only accept if one of them is valid; but we'll enforce uniqueness later
        # Given the structure, pos_avg must be 0
        pos_avg = 0
        if pos_avg not in possible_avg_positions:
            continue

        # Clue 1: Tall is Holly -> same house
        pos_tall = pos_mother['Holly']

        # Tall cannot conflict with avg or short
        if pos_tall in (pos_avg, pos_short):
            continue

        # Clue 6: Very short is Penny
        pos_very_short = pos_mother['Penny']
        # Very short cannot be same as avg or short
        if pos_very_short in (pos_avg, pos_short):
            continue
        # All four heights must be in distinct positions
        if len({pos_avg, pos_short, pos_tall, pos_very_short}) != 4:
            continue

        # Build heights per house
        heights = [None] * 5
        heights[pos_avg] = 'average'
        heights[pos_short] = 'short'
        heights[pos_tall] = 'tall'
        heights[pos_very_short] = 'very short'
        # Remaining house gets 'very tall'
        remaining_positions = [i for i in houses if heights[i] is None]
        if len(remaining_positions) != 1:
            continue
        heights[remaining_positions[0]] = 'very tall'

        # Clue 3: Gray is directly left of Janelle
        if pos_mother['Janelle'] == 0:
            continue
        pos_gray = pos_mother['Janelle'] - 1
        if pos_gray < 0:
            continue

        # Clue 12: Brown is somewhere left of Janelle (Arnold has brown hair)
        # We'll enforce via names placement (Arnold's house index < Janelle's house index)

        # Iterate over names permutations with Bob in the fifth house
        for names_perm in itertools.permutations(Names):
            if names_perm[4] != 'Bob':  # Clue 8
                continue

            # Clue 4 + 5: Eric has black hair and black is not in 4th house -> Eric not in house 4
            if names_perm[3] == 'Eric':
                continue

            # Clue 12: Arnold (brown hair) is to the left of Janelle (mother)
            pos_arnold = names_perm.index('Arnold')
            if not (pos_arnold < pos_mother['Janelle']):
                continue

            # The gray hair position must not be occupied by Eric/Peter/Arnold (they have fixed hair colors)
            if names_perm[pos_gray] in ('Eric', 'Peter', 'Arnold'):
                continue

            # Clue 7: Eric and gray are next to each other
            pos_eric = names_perm.index('Eric')
            if abs(pos_eric - pos_gray) != 1:
                continue

            # Build hair assignment
            hair = [None] * 5
            for i, nm in enumerate(names_perm):
                if nm == 'Eric':
                    hair[i] = 'black'
                elif nm == 'Peter':
                    hair[i] = 'red'
                elif nm == 'Arnold':
                    hair[i] = 'brown'

            # Set gray at pos_gray
            if hair[pos_gray] is not None and hair[pos_gray] != 'gray':
                continue
            hair[pos_gray] = 'gray'

            # Fill remaining hair as blonde
            used_hairs = {h for h in hair if h is not None}
            remaining_hairs = [h for h in Hairs if h not in used_hairs]
            if len(remaining_hairs) != 1:
                continue
            remaining_color = remaining_hairs[0]
            for i in range(5):
                if hair[i] is None:
                    hair[i] = remaining_color

            # Verify all hair colors unique
            if len(set(hair)) != 5:
                continue

            # Clue 4: black hair not in 4th house
            if hair[3] == 'black':
                continue

            # At this point, all constraints should be satisfied
            solution_rows = []
            for i in range(5):
                solution_rows.append([
                    str(i + 1),
                    names_perm[i],
                    heights[i],
                    mothers_perm[i],
                    hair[i]
                ])

            solutions.append({
                "solution": {
                    "header": ["House", "Name", "Height", "Mother", "HairColor"],
                    "rows": solution_rows
                }
            })

    # Expect a unique solution
    if not solutions:
        raise RuntimeError("No solution found.")
    # If multiple, choose the first (should be unique)
    return solutions[0]

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))