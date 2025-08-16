import json

def main():
    n = 5
    names = [None] * n
    smoothies = [None] * n
    nationalities = [None] * n

    # Assign from clues
    smoothies[1] = 'dragonfruit'  # Clue 2: second house (index 1)
    names[2] = 'Alice'            # Clue 10: third house (index 2)
    nationalities[2] = 'norwegian' # Clue 9: Alice is Norwegian
    smoothies[2] = 'watermelon'    # Clue 11: third house
    nationalities[0] = 'swede'     # Clue 6: Swede left of Dragonfruit (house 1)

    # Dane (Bob) must be in house 4 (index 3) based on Clue 7 and Clue 4
    nationalities[3] = 'dane'
    names[3] = 'Bob'              # Clue 8: Bob is the Dane

    # Clue 7: Two houses between Lime and Dane -> Lime in house 1 (index 0)
    smoothies[0] = 'lime'

    # Clue 4: Dane (house 4) adjacent to Brit -> Brit in house 5 (index 4)
    nationalities[4] = 'brit'

    # Clue 5: Desert not in fifth house -> Desert in house 4 (index 3), Cherry in house 5 (index 4)
    smoothies[3] = 'desert'
    smoothies[4] = 'cherry'

    # Clue 1: Dragonfruit (house 2) left of Eric -> Eric in house 5 (index 4)
    names[4] = 'Eric'

    # Clue 3: Peter not in first house -> Peter in house 2 (index 1), Arnold in house 1 (index 0)
    names[0] = 'Arnold'
    names[1] = 'Peter'

    # Remaining nationality: German for house 2 (index 1)
    nationalities[1] = 'german'

    # Prepare the solution dictionary
    solution_dict = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Nationality"],
            "rows": []
        }
    }

    for i in range(n):
        house_num = str(i + 1)
        row = [house_num, names[i], smoothies[i], nationalities[i]]
        solution_dict["solution"]["rows"].append(row)

    # Output the JSON
    print(json.dumps(solution_dict, indent=2))

if __name__ == "__main__":
    main()