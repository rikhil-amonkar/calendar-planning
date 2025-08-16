import json

def main():
    names = [None] * 6
    vacations = [None] * 6

    # Set knowns from clues
    names[1] = 'Eric'       # Clue 3: Eric in second house
    vacations[2] = 'cultural'  # Clue 4: cultural in third house
    names[2] = 'Peter'      # Clue 7: cultural is Peter
    vacations[3] = 'city'   # Clue 9: city in fourth house

    # Find positions for Bob and Arnold (Clue 5: Bob directly left of Arnold)
    candidate_pairs = []
    for i in range(5):
        j = i + 1
        if names[i] is not None and names[i] != 'Bob':
            continue
        if names[j] is not None and names[j] != 'Arnold':
            continue
        candidate_pairs.append((i, j))
    
    valid_pairs = []
    for (i, j) in candidate_pairs:
        if i == 3:
            continue
        valid_pairs.append((i, j))
    
    if not valid_pairs:
        error_output = {"error": "No valid positions found for Bob and Arnold"}
        print(json.dumps(error_output))
        return
    
    i_bob, i_arnold = valid_pairs[0]
    names[i_bob] = 'Bob'
    names[i_arnold] = 'Arnold'
    vacations[i_bob] = 'cruise'  # Clue 8: Bob likes cruises

    # Clue 2: Alice is left of Eric -> house1 (index0)
    if names[0] is None:
        names[0] = 'Alice'
    elif names[0] != 'Alice':
        error_output = {"error": "House1 must be Alice"}
        print(json.dumps(error_output))
        return

    # Assign Carol to the remaining house
    for idx in range(6):
        if names[idx] is None:
            names[idx] = 'Carol'
            break

    # Set beach vacation (Clue 1: cultural left of beach)
    vacations[5] = 'beach'  # House6 (index5) is the only position right of house3

    # Assign remaining vacations (mountain and camping)
    if vacations[0] is None and vacations[1] is None:
        vacations[0] = 'mountain'
        vacations[1] = 'camping'  # Clue 6: camping not in house1
    else:
        if vacations[0] is None:
            vacations[0] = 'mountain'
        elif vacations[0] == 'camping':
            error_output = {"error": "Camping cannot be in house1"}
            print(json.dumps(error_output))
            return
        if vacations[1] is None:
            vacations[1] = 'camping'

    # Build the solution rows
    rows = []
    for i in range(6):
        house_num = str(i + 1)
        name = names[i]
        vacation = vacations[i]
        rows.append([house_num, name, vacation])
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Vacation"],
            "rows": rows
        }
    }
    print(json.dumps(solution))

if __name__ == "__main__":
    main()