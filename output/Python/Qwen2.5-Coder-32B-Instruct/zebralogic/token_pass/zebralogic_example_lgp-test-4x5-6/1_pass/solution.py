import json

def is_valid(state, constraints):
    # Check if the current state satisfies all constraints
    for constraint in constraints:
        if not constraint(state):
            return False
    return True

def solve_puzzle():
    # Define the initial state
    houses = [{} for _ in range(4)]
    
    # Define the domains for each characteristic
    names = ['Peter', 'Eric', 'Alice', 'Arnold']
    educations = ['bachelor', 'high school', 'associate', 'master']
    music_genres = ['jazz', 'rock', 'pop', 'classical']
    colors = ['green', 'red', 'yellow', 'white']
    flowers = ['lilies', 'carnations', 'daffodils', 'roses']
    
    # Define the constraints
    constraints = [
        lambda s: next((h for h in s if h.get('Education') == 'bachelor' and h.get('Flower') == 'daffodils'), None),
        lambda s: not any(h.get('Flower') == 'carnations' for h in s[:1]),
        lambda s: next((h for h in s if h.get('Name') == 'Alice' and h.get('Education') == 'master'), None),
        lambda s: next((i for i, h in enumerate(s) if h.get('Education') == 'master' and i+1 < len(s) and s[i+1].get('MusicGenre') == 'classical'), None) is not None,
        lambda s: not any(h.get('Name') == 'Eric' for h in s[1:2]),
        lambda s: not any(h.get('Name') == 'Arnold' for h in s[2:3]),
        lambda s: next((i for i, h in enumerate(s) if h.get('Color') == 'yellow' and i+1 < len(s) and s[i+1].get('Flower') == 'roses'), None) is not None,
        lambda s: next((h for h in s if h.get('MusicGenre') == 'pop' and h.get('House') == '2'), None),
        lambda s: not any(h.get('Education') == 'associate' for h in s[3:4]),
        lambda s: not any(h.get('Flower') == 'carnations' for h in s[3:4]),
        lambda s: next((i for i, h in enumerate(s) if h.get('Color') == 'red' and i+1 < len(s) and s[i+1].get('Color') == 'white'), None) is not None,
        lambda s: next((h for h in s if h.get('Color') == 'red' and h.get('MusicGenre') == 'rock'), None),
        lambda s: next((h for h in s if h.get('Name') == 'Arnold' and h.get('Color') == 'yellow'), None),
        lambda s: next((h for h in s if h.get('Flower') == 'daffodils' and h.get('Color') == 'yellow'), None)
    ]
    
    def backtrack(index=0):
        if index == 4:
            return True
        
        for name in names:
            if any(h.get('Name') == name for h in houses):
                continue
            houses[index]['Name'] = name
            
            for education in educations:
                if any(h.get('Education') == education for h in houses):
                    continue
                houses[index]['Education'] = education
                
                for music_genre in music_genres:
                    if any(h.get('MusicGenre') == music_genre for h in houses):
                        continue
                    houses[index]['MusicGenre'] = music_genre
                    
                    for color in colors:
                        if any(h.get('Color') == color for h in houses):
                            continue
                        houses[index]['Color'] = color
                        
                        for flower in flowers:
                            if any(h.get('Flower') == flower for h in houses):
                                continue
                            houses[index]['Flower'] = flower
                            
                            houses[index]['House'] = str(index + 1)
                            
                            if is_valid(houses, constraints):
                                if backtrack(index + 1):
                                    return True
                            
                            del houses[index]['Flower']
                        
                        del houses[index]['Color']
                    
                    del houses[index]['MusicGenre']
                
                del houses[index]['Education']
            
            del houses[index]['Name']
        
        return False
    
    if backtrack():
        # Format the solution as JSON
        solution = {
            "solution": {
                "header": ["House", "Name", "Education", "MusicGenre", "Color", "Flower"],
                "rows": [[h['House'], h['Name'], h['Education'], h['MusicGenre'], h['Color'], h['Flower']] for h in houses]
            }
        }
        return json.dumps(solution, indent=2)
    else:
        return "No solution found"

# Solve the puzzle and print the solution
print(solve_puzzle())