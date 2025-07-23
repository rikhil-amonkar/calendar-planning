import itertools
import json

def main():
    total_days = 23
    city_days = {
        'Paris': 6,
        'Oslo': 5,
        'Porto': 7,
        'Geneva': 7,
        'Reykjavik': 2
    }
    direct_flights = [
        ('Paris', 'Oslo'),
        ('Geneva', 'Oslo'),
        ('Porto', 'Paris'),
        ('Geneva', 'Paris'),
        ('Geneva', 'Porto'),
        ('Paris', 'Reykjavik'),
        ('Reykjavik', 'Oslo'),
        ('Porto', 'Oslo')
    ]
    
    cities_list = list(city_days.keys())
    graph = {}
    for city in cities_list:
        graph[city] = []
    for a, b in direct_flights:
        if b not in graph[a]:
            graph[a].append(b)
        if a not in graph[b]:
            graph[b].append(a)
    
    fixed_segments = [
        {'start': 1, 'end': 7, 'city': 'Geneva'},
        {'start': 19, 'end': 23, 'city': 'Oslo'}
    ]
    
    intermediate_cities = [city for city in cities_list if city not in ['Geneva', 'Oslo']]
    found_perm = None
    for perm in itertools.permutations(intermediate_cities):
        A, B, C = perm
        if A not in graph['Geneva']:
            continue
        if B not in graph[A]:
            continue
        if C not in graph[B]:
            continue
        if 'Oslo' not in graph[C]:
            continue
        found_perm = perm
        break
    
    if found_perm is None:
        result = {"itinerary": []}
        print(json.dumps(result))
        return
    
    A, B, C = found_perm
    dA = city_days[A]
    dB = city_days[B]
    dC = city_days[C]
    
    seg1 = (1, 7, 'Geneva')
    end2 = 7 + dA - 1
    seg2 = (7, end2, A)
    end3 = end2 + dB - 1
    seg3 = (end2, end3, B)
    end4 = end3 + dC - 1
    seg4 = (end3, end4, C)
    seg5 = (19, 23, 'Oslo')
    
    segments = [seg1, seg2, seg3, seg4, seg5]
    itinerary_list = []
    for seg in segments:
        start, end, city = seg
        if start == end:
            day_range_str = f"Day {start}"
        else:
            day_range_str = f"Day {start}-{end}"
        itinerary_list.append({"day_range": day_range_str, "place": city})
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()