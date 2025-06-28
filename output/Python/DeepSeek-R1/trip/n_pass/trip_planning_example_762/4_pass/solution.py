import itertools
import json

def main():
    cities = ['Dublin', 'Madrid', 'Oslo', 'Vilnius', 'London', 'Berlin']
    durations = {
        'Dublin': 3,
        'Madrid': 2,
        'Oslo': 3,
        'Vilnius': 1,
        'London': 2,
        'Berlin': 2
    }
    
    graph = {
        'London': ['Madrid', 'Oslo', 'Dublin', 'Berlin'],
        'Madrid': ['London', 'Oslo', 'Dublin', 'Berlin'],
        'Oslo': ['Vilnius', 'Madrid', 'London', 'Berlin', 'Dublin'],
        'Vilnius': ['Oslo', 'Berlin'],
        'Berlin': ['Vilnius', 'Oslo', 'Madrid', 'London', 'Dublin'],
        'Dublin': ['Madrid', 'Oslo', 'London', 'Berlin']
    }
    
    valid_itineraries = []
    
    for perm in itertools.permutations(cities):
        # Check flight connections
        valid_flight = True
        for i in range(len(perm)-1):
            if perm[i+1] not in graph[perm[i]]:
                valid_flight = False
                break
        if not valid_flight:
            continue
        
        # Calculate day ranges
        starts = []
        ends = []
        current_start = 1
        for city in perm:
            dur = durations[city]
            end_day = current_start + dur - 1
            starts.append(current_start)
            ends.append(end_day)
            current_start = end_day + 1
        
        # Check total days
        if ends[-1] != 13:
            continue
        
        # Check Madrid constraint (within first 3 days)
        idx_madrid = perm.index('Madrid')
        if starts[idx_madrid] > 3:
            continue
        
        # Check Dublin constraint (start between 5-9)
        idx_dublin = perm.index('Dublin')
        if starts[idx_dublin] < 5 or starts[idx_dublin] > 9:
            continue
        
        # Check Berlin constraint (start <=7)
        idx_berlin = perm.index('Berlin')
        if starts[idx_berlin] > 7:
            continue
        
        # Build itinerary
        itinerary_list = []
        for i in range(len(perm)):
            day_range_str = f"Day {starts[i]}-{ends[i]}"
            itinerary_list.append({"day_range": day_range_str, "place": perm[i]})
        
        # Store with Berlin's start day for sorting
        valid_itineraries.append((starts[idx_berlin], itinerary_list))
    
    if valid_itineraries:
        # Select itinerary with earliest Berlin start
        valid_itineraries.sort(key=lambda x: x[0])
        best_itinerary = valid_itineraries[0][1]
        print(json.dumps({"itinerary": best_itinerary}))
    else:
        print(json.dumps({"error": "No valid itinerary found."}))

if __name__ == "__main__":
    main()