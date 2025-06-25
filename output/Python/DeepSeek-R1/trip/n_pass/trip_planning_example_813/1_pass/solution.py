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
    
    found = False
    result_itinerary = None
    
    for perm in itertools.permutations(cities):
        valid_sequence = True
        for idx in range(len(perm) - 1):
            current_city = perm[idx]
            next_city = perm[idx+1]
            if next_city not in graph.get(current_city, []):
                valid_sequence = False
                break
                
        if not valid_sequence:
            continue
            
        cum_durations = [0]
        total_so_far = 0
        for i in range(len(perm) - 1):
            total_so_far += duration_map[perm[i]]
            cum_durations.append(total_so_far)
        
        itinerary_segments = []
        valid_constraints = True
        for j in range(len(perm)):
            start_day = 1 + cum_durations[j] - j
            duration_here = duration_map[perm[j]]
            end_day = start_day + duration_here - 1
            day_range_str = f"Day {start_day}-{end_day}" if start_day != end_day else f"Day {start_day}"
            itinerary_segments.append({"day_range": day_range_str, "place": perm[j]})
            
            if perm[j] == 'London':
                if not (8 <= start_day <= 10):
                    valid_constraints = False
                    break
            elif perm[j] == 'Stuttgart':
                if not (5 <= start_day <= 9):
                    valid_constraints = False
                    break
                    
        if valid_constraints:
            found = True
            result_itinerary = itinerary_segments
            break
            
    if found:
        print(json.dumps({'itinerary': result_itinerary}))
    else:
        print(json.dumps({'itinerary': []}))

if __name__ == "__main__":
    main()