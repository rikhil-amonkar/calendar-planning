import itertools
import json

# Define the possible values for each category
names = ['Eric', 'Peter', 'Arnold']
mothers = ['Holly', 'Aniya', 'Janelle']
foods = ['pizza', 'grilled cheese', 'spaghetti']

solution = None

# Iterate through all permutations
for name_perm in itertools.permutations(names):
    for mother_perm in itertools.permutations(mothers):
        for food_perm in itertools.permutations(foods):
            # Clue 3: Eric's food is grilled cheese
            eric_pos = name_perm.index('Eric')
            if food_perm[eric_pos] != 'grilled cheese':
                continue
            # Clue 4: Peter's mother is Holly
            peter_pos = name_perm.index('Peter')
            if mother_perm[peter_pos] != 'Holly':
                continue
            # Clue 2: Eric's position directly left of Aniya's mother
            if eric_pos == 2:
                continue  # Can't have a house to the right
            if mother_perm[eric_pos + 1] != 'Aniya':
                continue
            # Clue 1: Spaghetti and Peter are adjacent
            spaghetti_pos = food_perm.index('spaghetti')
            if abs(spaghetti_pos - peter_pos) != 1:
                continue
            # All clues satisfied, build the solution
            solution = {
                "solution": {
                    "header": ["House", "Name", "Mother", "Food"],
                    "rows": []
                }
            }
            for house_num in range(1, 4):
                idx = house_num - 1
                row = [
                    str(house_num),
                    name_perm[idx],
                    mother_perm[idx],
                    food_perm[idx]
                ]
                solution["solution"]["rows"].append(row)
            # Output and exit
            print(json.dumps(solution))
            exit()

# If no solution is found (should not happen)
print(json.dumps({"solution": {}}))