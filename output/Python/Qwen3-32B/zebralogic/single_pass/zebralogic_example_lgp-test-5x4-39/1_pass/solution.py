import itertools
import json

# Generate all possible height configurations based on the constraints
possible_heights = []
for p in itertools.permutations(['very tall', 'average', 'short']):
    heights_candidate = [p[0], p[1], 'tall', p[2], 'very short']
    possible_heights.append(heights_candidate)

# Iterate through each possible height configuration
for heights in possible_heights:
    avg_house_index = heights.index('average')
    possible_gardening_positions = [avg_house_index - 1, avg_house_index + 1]
    for gardening_pos in possible_gardening_positions:
        if 0 <= gardening_pos < 5 and gardening_pos not in {1, avg_house_index}:
            # Assign hobbies: painting at index 1, cooking at avg_house_index, gardening at gardening_pos
            assigned_hobby_positions = {1, avg_house_index, gardening_pos}
            unassigned_hobby_positions = [i for i in range(5) if i not in assigned_hobby_positions]
            for hobby_perm in itertools.permutations(['photography', 'knitting']):
                hobby = [''] * 5
                hobby[1] = 'painting'
                hobby[avg_house_index] = 'cooking'
                hobby[gardening_pos] = 'gardening'
                for i, pos in enumerate(unassigned_hobby_positions):
                    hobby[pos] = hobby_perm[i]
                # Determine Bob's house (where hobby is 'photography')
                bob_house = hobby.index('photography')
                # Determine Peter's house (where height is 'short')
                house_peter = heights.index('short')
                # Check if Peter is in house 2 (index 1)
                if house_peter == 1:
                    continue
                # Assign names: Peter at house_peter, Bob at bob_house
                remaining_name_positions = [i for i in range(5) if i not in {house_peter, bob_house}]
                for name_perm in itertools.permutations(['Arnold', 'Eric', 'Alice']):
                    name = [''] * 5
                    name[house_peter] = 'Peter'
                    name[bob_house] = 'Bob'
                    for i, pos in enumerate(remaining_name_positions):
                        name[pos] = name_perm[i]
                    # Check if Eric is in house 5 (index 4)
                    if name[4] == 'Eric':
                        continue
                    # Check if Alice is to the right of Bob
                    alice_house = name.index('Alice')
                    bob_house_index = bob_house
                    if alice_house <= bob_house_index:
                        continue
                    # Assign foods: grilled cheese at index 2, stir fry at index 3
                    remaining_food_positions = [0, 1, 4]
                    for food_perm in itertools.permutations(['stew', 'pizza', 'spaghetti']):
                        # Check if house 1 (index 1) is 'spaghetti'
                        if food_perm[1] == 'spaghetti':
                            continue
                        foods = [''] * 5
                        foods[2] = 'grilled cheese'
                        foods[3] = 'stir fry'
                        foods[0] = food_perm[0]
                        foods[1] = food_perm[1]
                        foods[4] = food_perm[2]
                        # Check clue 6: Alice is directly left of pizza lover
                        pizza_pos = -1
                        for i in range(5):
                            if foods[i] == 'pizza':
                                pizza_pos = i
                                break
                        if pizza_pos == -1:
                            continue
                        if pizza_pos - 1 != alice_house:
                            continue
                        # All constraints satisfied, construct the solution
                        rows = []
                        for i in range(5):
                            house_num = str(i + 1)
                            rows.append([house_num, name[i], hobby[i], heights[i], foods[i]])
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Hobby", "Height", "Food"],
                                "rows": rows
                            }
                        }
                        print(json.dumps(solution, indent=2))
                        exit()