import itertools
import json

def main():
    # Define the graph of direct flights
    graph_edges = [
        ('London', 'Madrid'),
        ('Oslo', 'Vilnius'),
        ('Berlin', 'Vilnius'),
        ('Madrid', 'Oslo'),
        ('Madrid', 'Dublin'),
        ('London', 'Oslo'),
        ('Madrid', 'Berlin'),
        ('Berlin', 'Oslo'),
        ('Dublin', 'Oslo'),
        ('London', 'Dublin'),
        ('London', 'Berlin'),
        ('Berlin', 'Dublin')
    ]
    valid_edges = set(frozenset(edge) for edge in graph_edges)
    
    # Define the required days for each city
    days_required = {
        'London': 2,
        'Madrid': 2,
        'Oslo': 3,
        'Vilnius': 3,
        'Berlin': 5,
        'Dublin': 3
    }
    
    cities = list(days_required.keys())
    
    # Generate all permutations of the cities
    for perm in itertools.permutations(cities):
        # Check direct flight constraints between consecutive cities
        valid_sequence = True
        for i in range(len(perm) - 1):
            if frozenset({perm[i], perm[i+1]}) not in valid_edges:
                valid_sequence = False
                break
        if not valid_sequence:
            continue
            
        # Calculate start and end days for each city in the permutation
        starts = [1]
        for i in range(len(perm) - 1):
            starts.append(starts[i] + days_required[perm[i]] - 1)
        
        # Check event constraints
        madrid_index = perm.index('Madrid')
        madrid_start = starts[madrid_index]
        madrid_end = madrid_start + days_required['Madrid'] - 1
        if not (madrid_start <= 3 and madrid_end >= 2):
            continue
            
        berlin_index = perm.index('Berlin')
        berlin_start = starts[berlin_index]
        berlin_end = berlin_start + days_required['Berlin'] - 1
        if not (berlin_start <= 7 and berlin_end >= 3):
            continue
            
        dublin_index = perm.index('Dublin')
        dublin_start = starts[dublin_index]
        dublin_end = dublin_start + days_required['Dublin'] - 1
        if not (dublin_start <= 9 and dublin_end >= 7):
            continue
            
        # If we reach here, the permutation is valid
        itinerary = []
        for idx, city in enumerate(perm):
            start_day = starts[idx]
            end_day = start_day + days_required[city] - 1
            if start_day == end_day:
                day_range = f"Day {start_day}"
            else:
                day_range = f"Day {start_day}-{end_day}"
            itinerary.append({"day_range": day_range, "place": city})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
        return
    
    # If no valid itinerary found
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()