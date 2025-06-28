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
        valid_connection = True
        for i in range(len(perm)-1):
            edge_key = tuple(sorted((perm[i], perm[i+1])))
            if edge_key not in edges:
                valid_connection = False
                break
        if not valid_connection:
            continue
        
        starts = []
        ends = []
        total_so_far = 0
        for i, city in enumerate(perm):
            if i == 0:
                s = 1
            else:
                s = 1 + total_so_far - i
            d = durations[city]
            e = s + d - 1
            starts.append(s)
            ends.append(e)
            total_so_far += d
        
        idx_frankfurt = perm.index('Frankfurt')
        if not (starts[idx_frankfurt] <= 5 and ends[idx_frankfurt] >= 6):
            continue
        
        idx_mykonos = perm.index('Mykonos')
        if not (starts[idx_mykonos] <= 12 and ends[idx_mykonos] >= 10):
            continue
        
        idx_manchester = perm.index('Manchester')
        if not (starts[idx_manchester] <= 18 and ends[idx_manchester] >= 15):
            continue
        
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