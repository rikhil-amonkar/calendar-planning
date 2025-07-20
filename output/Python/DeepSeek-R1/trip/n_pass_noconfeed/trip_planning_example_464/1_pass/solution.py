import itertools
import json

def main():
    # Define the durations for each city
    durations = {
        'Krakow': 5,
        'Frankfurt': 4,
        'Oslo': 3,
        'Dubrovnik': 5,
        'Naples': 5
    }
    
    # Define the direct flight graph (undirected)
    graph = {
        'Dubrovnik': {'Oslo', 'Frankfurt', 'Naples'},
        'Oslo': {'Dubrovnik', 'Frankfurt', 'Krakow', 'Naples'},
        'Frankfurt': {'Dubrovnik', 'Oslo', 'Krakow', 'Naples'},
        'Krakow': {'Frankfurt', 'Oslo'},
        'Naples': {'Dubrovnik', 'Oslo', 'Frankfurt'}
    }
    
    cities = list(durations.keys())
    result_itinerary = None
    
    # Generate all permutations of the cities
    for perm in itertools.permutations(cities):
        # Check flight connections between consecutive cities
        valid_connection = True
        for i in range(len(perm) - 1):
            if perm[i+1] not in graph[perm[i]]:
                valid_connection = False
                break
        if not valid_connection:
            continue
        
        # Calculate start days for each city in the permutation
        start_days = [1]
        for i in range(1, len(perm)):
            next_start = start_days[i-1] + durations[perm[i-1]] - 1
            start_days.append(next_start)
        
        # Check constraints for Dubrovnik and Oslo
        dubrovnik_ok = False
        oslo_ok = False
        for idx, city in enumerate(perm):
            if city == 'Dubrovnik':
                if start_days[idx] <= 9:
                    dubrovnik_ok = True
            elif city == 'Oslo':
                if 14 <= start_days[idx] <= 16:
                    oslo_ok = True
        
        if dubrovnik_ok and oslo_ok:
            # Build itinerary
            itinerary_list = []
            for i in range(len(perm)):
                start = start_days[i]
                end = start + durations[perm[i]] - 1
                day_range = f"Day {start}-{end}"
                itinerary_list.append({
                    "day_range": day_range,
                    "place": perm[i]
                })
            result_itinerary = {"itinerary": itinerary_list}
            break
    
    # Output the result as JSON
    if result_itinerary is None:
        # Fallback in case no valid itinerary is found (should not happen per constraints)
        print(json.dumps({"itinerary": []}))
    else:
        print(json.dumps(result_itinerary))

if __name__ == "__main__":
    main()