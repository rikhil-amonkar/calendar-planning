import itertools
import json

def format_day_range(start, end):
    if start == end:
        return f"Day {start}"
    else:
        return f"Day {start}-{end}"

def main():
    graph = {
        'Paris': ['Oslo', 'Porto', 'Geneva', 'Reykjavik'],
        'Oslo': ['Paris', 'Geneva', 'Porto', 'Reykjavik'],
        'Porto': ['Paris', 'Geneva', 'Oslo'],
        'Geneva': ['Paris', 'Oslo', 'Porto'],
        'Reykjavik': ['Paris', 'Oslo']
    }
    
    required_durations = {
        'Paris': 6,
        'Porto': 7,
        'Reykjavik': 2
    }
    
    middle_cities = ['Paris', 'Porto', 'Reykjavik']
    
    for perm in itertools.permutations(middle_cities):
        A, B, C = perm
        if A in graph['Geneva'] and B in graph[A] and C in graph[B] and 'Oslo' in graph[C]:
            d1 = required_durations[A]
            d2 = required_durations[B]
            d3 = required_durations[C]
            if d1 + d2 + d3 != 15:
                continue
                
            s1 = 7
            e1 = s1 + d1 - 1
            s2 = e1
            e2 = s2 + d2 - 1
            s3 = e2
            e3 = s3 + d3 - 1
            
            if e3 != 19:
                continue
                
            itinerary = []
            itinerary.append({'day_range': format_day_range(1, 7), 'place': 'Geneva'})
            itinerary.append({'day_range': format_day_range(s1, e1), 'place': A})
            itinerary.append({'day_range': format_day_range(s2, e2), 'place': B})
            itinerary.append({'day_range': format_day_range(s3, e3), 'place': C})
            itinerary.append({'day_range': format_day_range(19, 23), 'place': 'Oslo'})
            
            print(json.dumps({'itinerary': itinerary}, indent=None))
            return
            
    print(json.dumps({'itinerary': []}))

if __name__ == '__main__':
    main()