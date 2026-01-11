import json

def solve_puzzle():
    # Define possible values for each attribute
    names = ['Eric', 'Arnold']
    house_styles = ['victorian', 'colonial']
    smoothies = ['cherry', 'desert']
    pets = ['dog', 'cat']

    # Initialize houses
    houses = [{'name': None, 'house_style': None, 'smoothie': None, 'pet': None} for _ in range(2)]

    # Function to check constraints
    def is_valid(houses):
        # Clue 1: The person who likes Cherry smoothies is the person who owns a dog.
        if any(h['smoothie'] == 'cherry' and h['pet'] != 'dog' for h in houses):
            return False
        if any(h['pet'] == 'dog' and h['smoothie'] != 'cherry' for h in houses):
            return False
        
        # Clue 2: The person residing in a Victorian house is the person who owns a dog.
        if any(h['house_style'] == 'victorian' and h['pet'] != 'dog' for h in houses):
            return False
        if any(h['pet'] == 'dog' and h['house_style'] != 'victorian' for h in houses):
            return False
        
        # Clue 3: The person residing in a Victorian house is somewhere to the left of Eric.
        victorian_index = next((i for i, h in enumerate(houses) if h['house_style'] == 'victorian'), None)
        eric_index = next((i for i, h in enumerate(houses) if h['name'] == 'Eric'), None)
        if victorian_index is not None and eric_index is not None and victorian_index >= eric_index:
            return False
        
        return True

    # Backtracking function to try all combinations
    def backtrack(index):
        if index == 2:
            if is_valid(houses):
                return houses
            return None
        
        for name in names:
            if any(h['name'] == name for h in houses[:index]):
                continue
            houses[index]['name'] = name
            
            for house_style in house_styles:
                if any(h['house_style'] == house_style for h in houses[:index]):
                    continue
                houses[index]['house_style'] = house_style
                
                for smoothie in smoothies:
                    if any(h['smoothie'] == smoothie for h in houses[:index]):
                        continue
                    houses[index]['smoothie'] = smoothie
                    
                    for pet in pets:
                        if any(h['pet'] == pet for h in houses[:index]):
                            continue
                        houses[index]['pet'] = pet
                        
                        result = backtrack(index + 1)
                        if result is not None:
                            return result
                        
        return None

    # Start backtracking from the first house
    solution = backtrack(0)

    # Format the solution as JSON
    if solution:
        rows = [[str(i+1), h['name'], h['house_style'], h['smoothie'], h['pet']] for i, h in enumerate(solution)]
        json_output = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "Smoothie", "Pet"],
                "rows": rows
            }
        }
        return json.dumps(json_output, indent=2)
    else:
        return "No solution found"

# Solve the puzzle and print the result
print(solve_puzzle())