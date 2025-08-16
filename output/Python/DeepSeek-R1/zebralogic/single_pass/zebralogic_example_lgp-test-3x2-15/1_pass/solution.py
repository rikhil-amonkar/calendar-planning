import json

def main():
    # Initialize attributes
    houses = [1, 2, 3]
    n = len(houses)
    names = [None] * n
    heights = [None] * n
    
    # Apply clue 2: The person who is short is in the first house.
    heights[0] = 'short'
    
    # Apply clue 3: One house between short and very short -> very short must be in house 3
    heights[2] = 'very short'
    # Remaining house gets average height
    heights[1] = 'average'
    
    # Apply clue 4: Arnold and very short are next to each other -> Arnold must be in house 2
    names[1] = 'Arnold'
    
    # Apply clue 1: Peter is right of Eric -> Eric in house 1, Peter in house 3
    names[0] = 'Eric'
    names[2] = 'Peter'
    
    # Build solution rows
    rows = []
    for i in range(n):
        house_num = str(i+1)
        rows.append([house_num, names[i], heights[i]])
    
    # Create solution dictionary
    solution_dict = {
        "solution": {
            "header": ["House", "Name", "Height"],
            "rows": rows
        }
    }
    
    # Output JSON
    print(json.dumps(solution_dict))

if __name__ == "__main__":
    main()