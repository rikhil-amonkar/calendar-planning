import itertools
import json

def main():
    cities = ['Seville', 'Vilnius', 'Santorini', 'London', 'Stuttgart', 'Dublin', 'Frankfurt']
    duration_map = {
        'Seville': 5,
        'Vilnius': 3,
        'Santorini': 2,
        'London': 2,
        'Stuttgart': 3,
        'Dublin': 3,
        'Frankfurt': 5
    }

    edges = [
        ('Frankfurt', 'Dublin'),
        ('Frankfurt', 'London'),
        ('London', 'Dublin'),
        ('Vilnius', 'Frankfurt'),
        ('Frankfurt', 'Stuttgart'),
        ('Dublin', 'Seville'),
        ('London', 'Santorini'),
        ('Stuttgart', 'London'),
        ('Santorini', 'Dublin')
    ]
    
    graph = {}
    for u, v in edges:
        if u not in graph:
            graph[u] = []
        if v not in graph:
            graph[v] = []
        graph[u].append(v)
        graph[v].append(u)
    
    fixed_start = 'Seville'
    fixed_end = 'Vilnius'
    other_cities = [city for city in cities if city != fixed_start and city != fixed_end]
    
    n = len(other_cities)
    found = False
    result_itinerary = None
    
    for r in range(1, n+1):
        for subset in itertools.combinations(other_cities, r):
            total_duration = sum(duration_map[city] for city in subset)
            if total_duration != 9:
                continue
                
            for perm in itertools.permutations(subset):
                sequence = [fixed_start] + list(perm) + [fixed_end]
                valid_sequence = True
                for i in range(len(sequence)-1):
                    current = sequence[i]
                    next_city = sequence[i+1]
                    if next_city not in graph.get(current, []):
                        valid_sequence = False
                        break
                if not valid_sequence:
                    continue
                    
                current_start = 1
                itinerary_segments = []
                skip_sequence = False
                for city in sequence:
                    duration = duration_map[city]
                    end_day = current_start + duration - 1
                    if city == 'London':
                        if current_start < 8 or current_start > 10:
                            skip_sequence = True
                            break
                    if city == 'Stuttgart':
                        if current_start < 5 or current_start > 9:
                            skip_sequence = True
                            break
                    if duration > 1:
                        day_range_str = f"Day {current_start}-{end_day}"
                    else:
                        day_range_str = f"Day {current_start}"
                    itinerary_segments.append({"day_range": day_range_str, "place": city})
                    current_start = end_day + 1
                    
                if skip_sequence:
                    continue
                    
                found = True
                result_itinerary = itinerary_segments
                break
            if found:
                break
        if found:
            break
            
    if found:
        print(json.dumps({'itinerary': result_itinerary}))
    else:
        print(json.dumps({'itinerary': []}))

if __name__ == "__main__":
    main()