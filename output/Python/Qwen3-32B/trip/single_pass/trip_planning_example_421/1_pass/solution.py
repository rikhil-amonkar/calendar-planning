import itertools
import json

def main():
    # Define durations for each city
    durations = {
        'Nice': 5,
        'Krakow': 6,
        'Dublin': 7,
        'Lyon': 4,
        'Frankfurt': 2
    }
    
    # Define adjacency list for direct flights
    adj = {
        'Nice': ['Dublin', 'Frankfurt', 'Lyon'],
        'Dublin': ['Nice', 'Frankfurt', 'Krakow', 'Lyon'],
        'Frankfurt': ['Dublin', 'Krakow', 'Lyon'],
        'Krakow': ['Dublin', 'Frankfurt'],
        'Lyon': ['Frankfurt', 'Dublin', 'Nice']
    }
    
    # Cities to permute between Nice and Frankfurt
    intermediate_cities = ['Krakow', 'Dublin', 'Lyon']
    valid_order = None
    
    # Find a valid path from Nice to Frankfurt through the intermediate cities
    for perm in itertools.permutations(intermediate_cities):
        path = ['Nice'] + list(perm) + ['Frankfurt']
        valid = True
        for i in range(len(path) - 1):
            current = path[i]
            next_city = path[i+1]
            if next_city not in adj[current]:
                valid = False
                break
        if valid:
            valid_order = path
            break
    
    if valid_order is None:
        print(json.dumps({"error": "No valid itinerary found."}))
        return
    
    # Compute the itinerary with day ranges
    itinerary = []
    start_day = 1
    for city in valid_order:
        duration = durations[city]
        end_day = start_day + duration - 1
        day_range = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city})
        start_day = end_day  # Next city starts on the same day (end of previous)
    
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()