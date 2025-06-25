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
    
    # Fixed first and last cities
    first_city = 'Porto'
    last_city = 'Manchester'
    other_cities = ['Geneva', 'Mykonos', 'Hamburg', 'Naples', 'Frankfurt']
    
    found = False
    itinerary_list = []
    
    for perm_middle in itertools.permutations(other_cities):
        perm = [first_city] + list(perm_middle) + [last_city]
        valid_connection = True
        for i in range(len(perm)-1):
            edge_key = tuple(sorted((perm[i], perm[i+1])))
            if edge_key not in edges:
                valid_connection = False
                break
        if not valid_connection:
            continue
        
        starts = [1]
        for i in range(1, len(perm)):
            start_next = starts[i-1] + durations[perm[i-1]] - 1  # Corrected calculation
            starts.append(start_next)
        
        s_manchester = starts[-1]
        if s_manchester != 15:
            continue
            
        idx_frankfurt = perm.index('Frankfurt')
        s_frankfurt = starts[idx_frankfurt]
        if not (4 <= s_frankfurt <= 6):
            continue
            
        idx_mykonos = perm.index('Mykonos')
        s_mykonos = starts[idx_mykonos]
        if not (8 <= s_mykonos <= 12):
            continue
        
        for i in range(len(perm)):
            s = starts[i]
            d = durations[perm[i]]
            e = s + d - 1
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