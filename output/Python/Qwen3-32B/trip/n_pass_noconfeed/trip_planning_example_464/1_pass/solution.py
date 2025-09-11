import itertools
import json

def main():
    cities = ['Krakow', 'Frankfurt', 'Oslo', 'Dubrovnik', 'Naples']
    durations = {
        'Krakow': 5,
        'Frankfurt': 4,
        'Oslo': 3,
        'Dubrovnik': 5,
        'Naples': 5
    }
    
    # Define flight graph based on direct connections
    flight_graph = {
        'Dubrovnik': ['Oslo', 'Frankfurt', 'Naples'],
        'Frankfurt': ['Krakow', 'Oslo', 'Dubrovnik', 'Naples'],
        'Krakow': ['Frankfurt', 'Oslo'],
        'Oslo': ['Frankfurt', 'Krakow', 'Dubrovnik', 'Naples'],
        'Naples': ['Dubrovnik', 'Frankfurt', 'Oslo'],
    }
    
    # Find valid permutation
    for perm in itertools.permutations(cities):
        # Check flight connections between consecutive cities
        valid = True
        for i in range(len(perm) - 1):
            current = perm[i]
            next_city = perm[i+1]
            if next_city not in flight_graph[current]:
                valid = False
                break
        if not valid:
            continue
        
        # Compute day ranges for each city in the permutation
        day_ranges = []
        current_start = 1
        for city in perm:
            duration = durations[city]
            end_day = current_start + duration - 1
            day_ranges.append((current_start, end_day))
            current_start = end_day  # next city starts on this day
        
        # Check Dubrovnik's day range (must be Day 5-9)
        d_index = perm.index('Dubrovnik')
        d_start, d_end = day_ranges[d_index]
        if d_start != 5 or d_end != 9:
            continue
        
        # Check Oslo's day range (must be Day 16-18)
        o_index = perm.index('Oslo')
        o_start, o_end = day_ranges[o_index]
        if o_start != 16 or o_end != 18:
            continue
        
        # Construct the itinerary JSON
        itinerary = []
        for i in range(len(perm)):
            city = perm[i]
            start, end = day_ranges[i]
            day_range_str = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range_str, "place": city})
        
        print(json.dumps({"itinerary": itinerary}))
        return
    
    # If no valid itinerary is found
    print(json.dumps({"error": "No valid itinerary found"}))

if __name__ == "__main__":
    main()