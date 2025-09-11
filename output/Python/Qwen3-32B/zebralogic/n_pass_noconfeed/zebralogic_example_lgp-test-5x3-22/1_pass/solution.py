import itertools
import json

# Define the possible values
names = ['Arnold', 'Eric', 'Bob', 'Peter', 'Alice']
smoothie_options = ['desert', 'watermelon', 'lime', 'cherry', 'dragonfruit']
nationality_options = ['german', 'swede', 'norwegian', 'dane', 'brit']

valid_solution = None

for name_perm in itertools.permutations(names):
    # Check name constraints: Alice in house 3 (index 2), Peter not in house 1 (index 0)
    if name_perm[2] != 'Alice' or name_perm[0] == 'Peter':
        continue

    for smoothie_perm in itertools.permutations(smoothie_options):
        # Check smoothie constraints: dragonfruit in house 2 (index 1), watermelon in house 3 (index 2), desert not in house 5 (index 4)
        if (smoothie_perm[1] != 'dragonfruit' or
            smoothie_perm[2] != 'watermelon' or
            smoothie_perm[4] == 'desert'):
            continue

        for nationality_perm in itertools.permutations(nationality_options):
            # Check nationality constraints: swede in house 1 (index 0)
            if nationality_perm[0] != 'swede':
                continue

            # Check clue 8: Bob is Dane
            bob_index = None
            for i in range(5):
                if name_perm[i] == 'Bob':
                    bob_index = i
                    break
            if nationality_perm[bob_index] != 'dane':
                continue

            # Check clue 9: Alice's nationality is norwegian
            if nationality_perm[2] != 'norwegian':
                continue

            # Check clue 4: Dane and Brit are next to each other
            dane_pos = None
            brit_pos = None
            for i in range(5):
                if nationality_perm[i] == 'dane':
                    dane_pos = i
                if nationality_perm[i] == 'brit':
                    brit_pos = i
            if abs(dane_pos - brit_pos) != 1:
                continue

            # Check clue 7: two houses between Lime and Dane
            lime_pos = None
            for i in range(5):
                if smoothie_perm[i] == 'lime':
                    lime_pos = i
                    break
            if abs(lime_pos - dane_pos) != 3:
                continue

            # Check clue 1: Dragonfruit lover is left of Eric
            eric_pos = None
            for i in range(5):
                if name_perm[i] == 'Eric':
                    eric_pos = i
                    break
            if eric_pos is None or eric_pos <= 1:  # Dragonfruit is at index 1 (house 2)
                continue

            # All constraints satisfied
            valid_solution = (name_perm, smoothie_perm, nationality_perm)
            break
        if valid_solution:
            break
    if valid_solution:
        break

# Construct the solution JSON
solution_data = {
    "solution": {
        "header": ["House", "Name", "Smoothie", "Nationality"],
        "rows": []
    }
}

if valid_solution:
    name_perm, smoothie_perm, nationality_perm = valid_solution
    for i in range(5):
        house_num = str(i + 1)
        name = name_perm[i]
        smoothie = smoothie_perm[i]
        nationality = nationality_perm[i]
        solution_data["solution"]["rows"].append([house_num, name, smoothie, nationality])

print(json.dumps(solution_data, indent=2))