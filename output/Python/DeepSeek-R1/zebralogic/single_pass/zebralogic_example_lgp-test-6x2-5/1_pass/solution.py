import json

def main():
    n_houses = 6
    names = [None] * n_houses
    vacations = [None] * n_houses

    # Apply clue 3: Eric is in the second house (index1)
    names[1] = 'Eric'
    
    # Apply clue 4: cultural tours in third house (index2)
    vacations[2] = 'cultural'
    
    # Apply clue 7: the person with cultural tours is Peter (so house3: Peter)
    names[2] = 'Peter'
    
    # Apply clue 9: city breaks in fourth house (index3)
    vacations[3] = 'city'
    
    # Apply clue 2: Eric is right of Alice -> Alice must be in house1 (index0)
    names[0] = 'Alice'
    
    # Remaining names: Bob, Carol, Arnold for indices 3,4,5 (houses 4,5,6)
    # Clue 5: Bob is directly left of Arnold -> they must be consecutive. 
    # Clue 8: Bob has cruise. Since house4 (index3) has city vacation, Bob cannot be there.
    # Therefore, Bob must be at index4 (house5) and Arnold at index5 (house6). Carol at index3 (house4).
    names[3] = 'Carol'
    names[4] = 'Bob'
    names[5] = 'Arnold'
    
    # Apply clue 8: Bob has cruise -> house5 (index4) vacation is cruise
    vacations[4] = 'cruise'
    
    # Apply clue 1: cultural tours (index2) is left of beach -> beach must be at an index > 2.
    # Only index5 (house6) is available and >2.
    vacations[5] = 'beach'
    
    # Remaining vacations: mountain and camping for indices0 and 1.
    # Apply clue 6: camping not in first house -> index0 (house1) cannot be camping -> must be mountain.
    vacations[0] = 'mountain'
    vacations[1] = 'camping'
    
    # Build the solution structure
    header = ["House", "Name", "Vacation"]
    rows = []
    for i in range(n_houses):
        house_num = str(i+1)
        row = [house_num, names[i], vacations[i]]
        rows.append(row)
    
    solution_dict = {
        "header": header,
        "rows": rows
    }
    
    result = {
        "solution": solution_dict
    }
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()