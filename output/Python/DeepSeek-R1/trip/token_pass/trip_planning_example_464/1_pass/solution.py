import itertools
import json

def main():
    # Define the required days for each city
    required_days = {
        'Krakow': 5,
        'Frankfurt': 4,
        'Oslo': 3,
        'Dubrovnik': 5,
        'Naples': 5
    }
    
    # Define the direct flight connections (undirected graph)
    graph = {
        'Dubrovnik': ['Oslo', 'Frankfurt', 'Naples'],
        'Frankfurt': ['Krakow', 'Oslo', 'Dubrovnik', 'Naples'],
        'Krakow': ['Frankfurt', 'Oslo'],
        'Naples': ['Oslo', 'Dubrovnik', 'Frankfurt'],
        'Oslo': ['Dubrovnik', 'Frankfurt', 'Krakow', 'Naples']
    }
    
    # Cities to permute (excluding Oslo since it's fixed at the end)
    cities = ['Krakow', 'Frankfurt', 'Dubrovnik', 'Naples']
    
    # Generate all permutations of the cities
    for perm in itertools.permutations(cities):
        # Check flight connections between consecutive cities in the permutation
        valid_connection = True
        for i in range(len(perm) - 1):
            if perm[i+1] not in graph[perm[i]]:
                valid_connection = False
                break
        if not valid_connection:
            continue
            
        # Check connection from the last city to Oslo
        if 'Oslo' not in graph[perm[-1]]:
            continue
            
        # Calculate transition days
        d1 = required_days[perm[0]]
        d2 = d1 + required_days[perm[1]] - 1
        d3 = d2 + required_days[perm[2]] - 1
        d4 = d3 + required_days[perm[3]] - 1
        
        # We must end at day 16 to start Oslo on day 16
        if d4 != 16:
            continue
            
        # Check Dubrovnik constraint: must be between day 5 and 9
        dubrovnik_index = perm.index('Dubrovnik') if 'Dubrovnik' in perm else -1
        overlap = False
        if dubrovnik_index == 0:
            if d1 >= 5:
                overlap = True
        elif dubrovnik_index == 1:
            if max(d1, 5) <= min(d2, 9):
                overlap = True
        elif dubrovnik_index == 2:
            if max(d2, 5) <= min(d3, 9):
                overlap = True
        elif dubrovnik_index == 3:
            if d3 <= 9:
                overlap = True
                
        if not overlap:
            continue
            
        # Found valid itinerary
        full_sequence = list(perm) + ['Oslo']
        itinerary = []
        current_day = 1
        for idx, city in enumerate(full_sequence):
            days_needed = required_days[city]
            end_day = current_day + days_needed - 1
            itinerary.append({
                "day_range": f"Day {current_day}-{end_day}",
                "place": city
            })
            current_day = end_day
            
        print(json.dumps({"itinerary": itinerary}))
        return
        
    # If no valid itinerary found (should not happen given constraints)
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()