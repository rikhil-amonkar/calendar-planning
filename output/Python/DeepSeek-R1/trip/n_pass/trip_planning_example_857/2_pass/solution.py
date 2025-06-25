import itertools
import json

def main():
    durations = {
        'Porto': 2,
        'Geneva': 3,
        'Mykonos': 3,
        'Manchester': 4,
        'Hamburg': 5,
        'Naples': 5,
        'Frankfurt': 2
    }

    edge_list = [
        ('Hamburg', 'Frankfurt'),
        ('Naples', 'Mykonos'),
        ('Hamburg', 'Porto'),
        ('Hamburg', 'Geneva'),
        ('Mykonos', 'Geneva'),
        ('Frankfurt', 'Geneva'),
        ('Frankfurt', 'Porto'),
        ('Geneva', 'Porto'),
        ('Geneva', 'Manchester'),
        ('Naples', 'Manchester'),
        ('Frankfurt', 'Naples'),
        ('Frankfurt', 'Manchester'),
        ('Naples', 'Geneva'),
        ('Porto', 'Manchester'),
        ('Hamburg', 'Manchester')
    ]
    edges = {tuple(sorted(pair)) for pair in edge_list}
    
    cities = list(durations.keys())
    found = False
    itinerary_list = []
    
    for perm in itertools.permutations(cities):
        # Check flight connections
        valid_connection = True
        for i in range(len(perm)-1):
            edge_key = tuple(sorted((perm[i], perm[i+1])))
            if edge_key not in edges:
                valid_connection = False
                break
        if not valid_connection:
            continue
        
        # Assign contiguous non-overlapping days
        starts = []
        ends = []
        current_day = 1
        for city in perm:
            d = durations[city]
            start = current_day
            end = current_day + d - 1
            starts.append(start)
            ends.append(end)
            current_day = end + 1  # Next city starts the following day
        
        # Get indices for constrained cities
        try:
            idx_frankfurt = perm.index('Frankfurt')
            idx_mykonos = perm.index('Mykonos')
            idx_manchester = perm.index('Manchester')
        except ValueError:
            continue
        
        # Check constraints (partial overlap)
        frankfurt_ok = (starts[idx_frankfurt] <= 6) and (ends[idx_frankfurt] >= 5)
        mykonos_ok = (starts[idx_mykonos] <= 12) and (ends[idx_mykonos] >= 10)
        manchester_ok = (starts[idx_manchester] <= 18) and (ends[idx_manchester] >= 15)
        
        if not (frankfurt_ok and mykonos_ok and manchester_ok):
            continue
        
        # Build itinerary
        for i in range(len(perm)):
            s = starts[i]
            e = ends[i]
            if s == e:
                day_range_str = f"Day {s}"
            else:
                day_range_str = f"Day {s}-{e}"
            itinerary_list.append({
                "day_range": day_range_str,
                "place": perm[i]
            })
        found = True
        break
    
    if not found:
        itinerary_list = []
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == '__main__':
    main()