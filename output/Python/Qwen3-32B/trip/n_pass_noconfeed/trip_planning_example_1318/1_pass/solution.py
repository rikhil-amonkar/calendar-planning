import json

def main():
    # Define cities and their required durations
    cities = {
        'Oslo': 2,
        'Helsinki': 2,
        'Edinburgh': 3,
        'Riga': 2,
        'Tallinn': 5,
        'Budapest': 5,
        'Vilnius': 5,
        'Porto': 5,
        'Geneva': 4,
    }
    
    # Define the flight graph (directed)
    flights = {
        'Porto': ['Oslo', 'Edinburgh', 'Geneva'],
        'Oslo': ['Porto', 'Edinburgh', 'Geneva', 'Riga', 'Helsinki', 'Budapest', 'Vilnius'],
        'Edinburgh': ['Budapest', 'Geneva', 'Porto', 'Helsinki', 'Oslo', 'Riga'],
        'Riga': ['Tallinn', 'Vilnius', 'Oslo', 'Helsinki'],
        'Tallinn': ['Helsinki', 'Oslo', 'Vilnius'],
        'Budapest': ['Geneva', 'Oslo'],
        'Vilnius': ['Helsinki', 'Oslo'],
        'Helsinki': ['Vilnius', 'Budapest', 'Geneva', 'Oslo', 'Edinburgh', 'Riga', 'Tallinn'],
        'Geneva': ['Oslo', 'Budapest', 'Porto'],
    }
    
    # List of all cities
    all_cities = list(cities.keys())
    
    # To store the valid itinerary
    valid_itinerary = None
    
    # Perform DFS to find a valid path
    def dfs(current_path, visited):
        nonlocal valid_itinerary
        if len(current_path) == 9:
            # Calculate start and end days
            start_days = [0] * 9
            end_days = [0] * 9
            start_days[0] = 1
            end_days[0] = start_days[0] + cities[current_path[0]] - 1
            for i in range(1, 9):
                start_days[i] = end_days[i-1]
                end_days[i] = start_days[i] + cities[current_path[i]] - 1
            
            # Check constraints
            tallinn_index = current_path.index('Tallinn') if 'Tallinn' in current_path else -1
            oslo_index = current_path.index('Oslo') if 'Oslo' in current_path else -1
            if tallinn_index != -1 and oslo_index != -1:
                if start_days[tallinn_index] == 4 and start_days[oslo_index] == 24:
                    # Valid itinerary found
                    valid_itinerary = current_path
                    return True
            return False
        else:
            current_city = current_path[-1]
            for next_city in flights[current_city]:
                if next_city not in visited:
                    current_path.append(next_city)
                    visited.add(next_city)
                    if dfs(current_path, visited):
                        return True
                    current_path.pop()
                    visited.remove(next_city)
            return False
    
    # Start DFS from each possible starting city
    for start_city in all_cities:
        current_path = [start_city]
        visited = set(current_path)
        if dfs(current_path, visited):
            break
    
    # Generate the itinerary JSON
    if valid_itinerary:
        start_days = [0] * 9
        end_days = [0] * 9
        start_days[0] = 1
        end_days[0] = start_days[0] + cities[valid_itinerary[0]] - 1
        for i in range(1, 9):
            start_days[i] = end_days[i-1]
            end_days[i] = start_days[i] + cities[valid_itinerary[i]] - 1
        
        itinerary = []
        for i in range(9):
            day_range = f"Day {start_days[i]}-{end_days[i]}"
            itinerary.append({"day_range": day_range, "place": valid_itinerary[i]})
        
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print(json.dumps({"error": "No valid itinerary found"}, indent=2))

if __name__ == "__main__":
    main()