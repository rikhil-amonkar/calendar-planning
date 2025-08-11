import json

def main():
    n = 5
    names = [None] * n
    heights = [None] * n

    # Apply clue 1: short in second house (house2, index1)
    heights[1] = 'short'
    
    # Apply clue 7: average in fifth house (house5, index4)
    heights[4] = 'average'
    
    # Apply clue 5: Alice directly left of average -> house4 (index3) is Alice
    names[3] = 'Alice'
    
    # Apply clue 2: Peter directly left of Bob. 
    # Given constraints, Peter must be in house2 (index1) and Bob in house3 (index2)
    names[1] = 'Peter'
    names[2] = 'Bob'
    
    # Apply clue 3: Eric left of Peter -> Eric in house1 (index0)
    names[0] = 'Eric'
    
    # The only name left is Arnold for house5 (index4)
    names[4] = 'Arnold'
    
    # Apply clue 4: very tall directly left of Peter -> very tall in house1 (index0)
    heights[0] = 'very tall'
    
    # Apply clue 6: short and very short are adjacent -> very short in house3 (index2)
    heights[2] = 'very short'
    
    # The only height left is tall for house4 (index3)
    heights[3] = 'tall'
    
    # Build the solution dictionary
    solution = {
        "header": ["House", "Name", "Height"],
        "rows": []
    }
    
    for i in range(n):
        house_num = str(i + 1)
        row = [house_num, names[i], heights[i]]
        solution["rows"].append(row)
    
    output = {"solution": solution}
    print(json.dumps(output))

if __name__ == "__main__":
    main()