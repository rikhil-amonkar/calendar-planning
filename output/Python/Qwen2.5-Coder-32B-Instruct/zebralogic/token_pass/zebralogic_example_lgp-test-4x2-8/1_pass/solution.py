import json

def is_valid_solution(houses):
    # Check clue 1: The person whose favorite color is green is in the third house.
    if houses[2][1] != 'green':
        return False
    
    # Check clue 2: Peter is in the first house.
    if houses[0][0] != 'Peter':
        return False
    
    # Check clue 3: There is one house between the person whose favorite color is red and the person who loves yellow.
    red_index = next((i for i, (_, color) in enumerate(houses) if color == 'red'), None)
    yellow_index = next((i for i, (_, color) in enumerate(houses) if color == 'yellow'), None)
    if abs(red_index - yellow_index) != 2:
        return False
    
    # Check clue 4: Arnold is directly left of Eric.
    arnold_index = next((i for i, (name, _) in enumerate(houses) if name == 'Arnold'), None)
    eric_index = next((i for i, (name, _) in enumerate(houses) if name == 'Eric'), None)
    if arnold_index is not None and eric_index is not None and arnold_index + 1 != eric_index:
        return False
    
    # Check clue 5: Eric is the person who loves yellow.
    if houses[eric_index][1] != 'yellow':
        return False
    
    return True

def solve(houses, index=0):
    if index == 4:
        if is_valid_solution(houses):
            return houses
        else:
            return None
    
    for name in ['Peter', 'Arnold', 'Alice', 'Eric']:
        for color in ['yellow', 'green', 'red', 'white']:
            if all(house[0] != name for house in houses[:index]) and all(house[1] != color for house in houses[:index]):
                houses[index] = (name, color)
                result = solve(houses, index + 1)
                if result is not None:
                    return result
                houses[index] = (None, None)
    
    return None

def main():
    houses = [(None, None)] * 4
    solution = solve(houses)
    
    if solution:
        json_solution = {
            "solution": {
                "header": ["House", "Name", "Color"],
                "rows": [[str(i+1), name, color] for i, (name, color) in enumerate(solution)]
            }
        }
        print(json.dumps(json_solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()