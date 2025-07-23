import json
import itertools

def main():
    cities_after_stockholm = ['Oslo', 'Stuttgart', 'Split', 'Geneva', 'Tallinn']
    days_required = {
        'Oslo': 5,
        'Stuttgart': 5,
        'Split': 3,
        'Geneva': 2,
        'Tallinn': 5
    }
    
    graph = {
        'Reykjavik': ['Stuttgart', 'Stockholm', 'Tallinn', 'Oslo'],
        'Stockholm': ['Reykjavik', 'Oslo', 'Stuttgart', 'Split', 'Geneva'],
        'Oslo': ['Reykjavik', 'Stockholm', 'Split', 'Geneva', 'Porto', 'Tallinn'],
        'Stuttgart': ['Reykjavik', 'Porto', 'Stockholm', 'Split'],
        'Split': ['Oslo', 'Stockholm', 'Stuttgart', 'Geneva'],
        'Geneva': ['Oslo', 'Stockholm', 'Porto', 'Split'],
        'Porto': ['Stuttgart', 'Oslo', 'Geneva'],
        'Tallinn': ['Reykjavik', 'Oslo']
    }
    
    valid_perm = None
    for perm in itertools.permutations(cities_after_stockholm):
        if perm[0] not in graph['Stockholm']:
            continue
        if perm[1] not in graph[perm[0]]:
            continue
        if perm[2] not in graph[perm[1]]:
            continue
        if perm[3] not in graph[perm[2]]:
            continue
        if perm[4] not in graph[perm[3]]:
            continue
        if perm[4] not in graph['Porto']:
            continue
        valid_perm = perm
        break

    if valid_perm is None:
        print('{"itinerary": []}')
        return

    itinerary = [
        {"day_range": "Day 1-2", "place": "Reykjavik"},
        {"day_range": "Day 2-4", "place": "Stockholm"}
    ]
    
    current_end = 4
    for city in valid_perm:
        duration = days_required[city]
        start_day = current_end
        end_day = start_day + duration - 1
        current_end = end_day + 1
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
    
    itinerary.append({"day_range": "Day 19-21", "place": "Porto"})
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == '__main__':
    main()