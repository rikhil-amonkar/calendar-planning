import itertools
import json

def main():
    # Define the required days for each city
    days_req = {
        'Venice': 5,
        'Salzburg': 4,
        'Stockholm': 2,
        'Frankfurt': 4,
        'Florence': 4,
        'Barcelona': 2,
        'Stuttgart': 3
    }
    
    # Define the direct flights as an undirected graph
    edges = [
        ('Barcelona', 'Frankfurt'),
        ('Florence', 'Frankfurt'),
        ('Stockholm', 'Barcelona'),
        ('Barcelona', 'Florence'),
        ('Venice', 'Barcelona'),
        ('Stuttgart', 'Barcelona'),
        ('Frankfurt', 'Salzburg'),
        ('Stockholm', 'Frankfurt'),
        ('Stuttgart', 'Stockholm'),
        ('Stuttgart', 'Frankfurt'),
        ('Venice', 'Stuttgart'),
        ('Venice', 'Frankfurt')
    ]
    
    # Build an adjacency list for the graph
    graph = {}
    cities = days_req.keys()
    for city in cities:
        graph[city] = []
    for u, v in edges:
        graph[u].append(v)
        graph[v].append(u)
    
    # We start with Venice
    start_city = 'Venice'
    remaining_cities = list(cities)
    remaining_cities.remove(start_city)
    
    # Generate all permutations of the remaining cities
    found_path = None
    for perm in itertools.permutations(remaining_cities):
        path = [start_city] + list(perm)
        valid = True
        for i in range(len(path) - 1):
            if path[i+1] not in graph[path[i]]:
                valid = False
                break
        if valid:
            found_path = path
            break
    
    if found_path is None:
        print(json.dumps({"itinerary": []}))
        return
    
    # Compute the day ranges for each city in the path
 itinerary = []
    current_day = 1
    for i, city in enumerate(found_path):
        duration = days_req[city]
        end_day = current_day + duration - 1
        if i < len(found_path) - 1:
            # The next city starts on the same day we travel
            # So we don't adjust current_day for the next city until after we set the range
            pass
        # Format the day range string
        if current_day == end_day:
            day_range_str = f"Day {current_day}"
        else:
            day_range_str = f"Day {current_day}-{end_day}"
        itinerary.append({"day_range": day_range_str, "place": city})
        current_day = end_day  # The next city starts on this day (travel day)
    
    # Output the itinerary as JSON
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()