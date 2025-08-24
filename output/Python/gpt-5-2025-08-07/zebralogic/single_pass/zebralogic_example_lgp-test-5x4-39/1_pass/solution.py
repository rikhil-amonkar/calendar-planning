import json
from itertools import permutations

def solve():
    houses = [0, 1, 2, 3, 4]  # indices 0..4 correspond to houses 1..5

    Names = ['Arnold', 'Peter', 'Eric', 'Alice', 'Bob']
    Hobbies = ['painting', 'cooking', 'knitting', 'gardening', 'photography']
    Heights = ['very tall', 'tall', 'very short', 'average', 'short']
    Foods = ['stew', 'grilled cheese', 'stir fry', 'spaghetti', 'pizza']

    # Helper to find index of a value in an array
    def pos(arr, val):
        return arr.index(val)

    # Constraint 12, 13: Fix heights at certain houses (5th very short, 3rd tall)
    # Build all height configurations consistent with these
    heights_solutions = []
    remaining_heights = ['very tall', 'average', 'short']
    for perm in permutations(remaining_heights):
        heights = [None]*5
        heights[2] = 'tall'         # house 3
        heights[4] = 'very short'   # house 5
        # Fill houses 1,2,4 (indices 0,1,3) with the permutation
        fill_indices = [0, 1, 3]
        for idx, h in zip(fill_indices, perm):
            heights[idx] = h
        heights_solutions.append(heights)

    # Constraint 11 with 2 and 13 already implies:
    # painting directly left of grilled cheese, and tall person eats grilled cheese.
    # Since tall is at house 3 (index 2), grilled cheese is at 3, and painting at 2 (index 1).
    # Also Constraint 4 implies stir fry at 4 (index 3).
    # Build food configurations consistent with those.
    food_solutions = []
    for perm in permutations(['stew', 'spaghetti', 'pizza']):
        foods = [None]*5
        foods[2] = 'grilled cheese'  # house 3
        foods[3] = 'stir fry'        # house 4
        foods[0], foods[1], foods[4] = perm  # houses 1,2,5
        # Constraint 7 (interpreted): spaghetti not in second house
        if foods[1] == 'spaghetti':
            continue
        # Constraint 6 will be checked later with names (Alice directly left of pizza)
        food_solutions.append(foods)

    # Build hobby configurations with painting at house 2 (index 1)
    hobby_solutions = []
    for perm in permutations(['cooking', 'knitting', 'gardening', 'photography']):
        hobbies = [None]*5
        hobbies[1] = 'painting'  # house 2
        # Fill remaining houses 1,3,4,5 (indices 0,2,3,4)
        fill_indices = [0, 2, 3, 4]
        for idx, h in zip(fill_indices, perm):
            hobbies[idx] = h
        hobby_solutions.append(hobbies)

    # Now search over combinations and enforce all cross-category constraints
    for heights in heights_solutions:
        # Constraint 2: grilled cheese eater is tall (will be checked when foods is chosen)
        # Constraint 5: cooking = average
        # Constraint 10: average next to gardening
        avg_pos = pos(heights, 'average')
        tall_pos = pos(heights, 'tall')
        very_short_pos = pos(heights, 'very short')  # already fixed at 4

        for foods in food_solutions:
            # Constraint 2: grilled cheese eater is tall
            if pos(foods, 'grilled cheese') != tall_pos:
                continue
            # Constraint 4: tall directly left of stir fry
            if tall_pos + 1 != pos(foods, 'stir fry'):
                continue

            for hobbies in hobby_solutions:
                # Constraint 11: painting directly left of grilled cheese
                # painting at index 1, grilled cheese at index 2 already enforced by construction and foods
                if pos(hobbies, 'painting') + 1 != pos(foods, 'grilled cheese'):
                    continue

                # Constraint 5: cooking = average
                if pos(hobbies, 'cooking') != avg_pos:
                    continue

                # Constraint 10: average next to gardening
                if abs(avg_pos - pos(hobbies, 'gardening')) != 1:
                    continue

                # Now assign names under remaining constraints
                # Precompute useful positions
                pizza_pos = pos(foods, 'pizza')
                photo_pos = pos(hobbies, 'photography')
                short_pos = pos(heights, 'short')

                # Prepare name slots
                names = [None]*5

                # Constraint 9: short is Peter
                peter_house = short_pos
                # Constraint 3: Peter not in second house
                if peter_house == 1:
                    continue
                names[peter_house] = 'Peter'

                # Constraint 6: Alice directly left of pizza
                if pizza_pos == 0:
                    continue
                alice_house = pizza_pos - 1
                if names[alice_house] is not None and names[alice_house] != 'Alice':
                    continue
                names[alice_house] = 'Alice'

                # Constraint 1: Bob is the photography enthusiast
                bob_house = photo_pos
                if names[bob_house] is not None and names[bob_house] != 'Bob':
                    continue
                names[bob_house] = 'Bob'

                # Constraint 14: Alice somewhere to the right of the photography enthusiast
                if alice_house <= photo_pos:
                    continue

                # Remaining names to place: Arnold, Eric
                remaining_names = [n for n in Names if n not in names]
                remaining_positions = [i for i in range(5) if names[i] is None]

                # Constraint 8: Eric not in fifth house
                # If index 4 is among remaining positions, ensure it's not assigned Eric
                solutions_found = []
                from itertools import permutations as perm_names
                for rem_perm in perm_names(remaining_names):
                    candidate = names[:]
                    ok = True
                    for idx, nm in zip(remaining_positions, rem_perm):
                        # Constraint 8: Eric not in fifth house (index 4)
                        if nm == 'Eric' and idx == 4:
                            ok = False
                            break
                        # Constraint 3 already handled for Peter; still ensure no conflict
                        candidate[idx] = nm
                    if not ok:
                        continue

                    # Final sanity checks (redundant but safe)
                    if candidate.count('Peter') != 1 or candidate.count('Alice') != 1 or candidate.count('Bob') != 1:
                        continue
                    if candidate[1] == 'Peter':  # Peter not in second
                        continue
                    if candidate[4] == 'Eric':   # Eric not in fifth
                        continue
                    # Bob at photography house
                    if candidate[bob_house] != 'Bob':
                        continue
                    # Alice left of pizza
                    if pos(candidate, 'Alice') + 1 != pizza_pos:
                        continue
                    # Alice to the right of photography
                    if pos(candidate, 'Alice') <= photo_pos:
                        continue
                    # Peter short
                    if pos(candidate, 'Peter') != short_pos:
                        continue

                    solutions_found.append(candidate)

                if solutions_found:
                    # Take the first valid complete solution
                    final_names = solutions_found[0]
                    # Build result rows
                    rows = []
                    for i in range(5):
                        house_num = str(i+1)
                        rows.append([
                            house_num,
                            final_names[i],
                            hobbies[i],
                            heights[i],
                            foods[i]
                        ])
                    return {
                        "solution": {
                            "header": ["House", "Name", "Hobby", "Height", "Food"],
                            "rows": rows
                        }
                    }

    raise RuntimeError("No solution found")

if __name__ == "__main__":
    result = solve()
    print(json.dumps(result, ensure_ascii=False, indent=2))