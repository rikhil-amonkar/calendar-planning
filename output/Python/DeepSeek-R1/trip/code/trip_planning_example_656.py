import json
from itertools import permutations

cities = {
    'Reykjavik': 5,
    'Istanbul': 4,
    'Edinburgh': 5,
    'Oslo': 2,
    'Stuttgart': 3,
    'Bucharest': 5
}

flights = {
    'Reykjavik': ['Oslo', 'Stuttgart'],
    'Oslo': ['Reykjavik', 'Istanbul', 'Bucharest', 'Edinburgh'],
    'Istanbul': ['Oslo', 'Bucharest', 'Stuttgart', 'Edinburgh'],
    'Bucharest': ['Oslo', 'Istanbul'],
    'Edinburgh': ['Stuttgart', 'Istanbul', 'Oslo'],
    'Stuttgart': ['Edinburgh', 'Istanbul']
}

def check_constraints(day_ranges, order):
    ist_start, ist_end = None, None
    osl_start, osl_end = None, None
    for i, city in enumerate(order):
        s, e = day_ranges[i]
        if city == 'Istanbul':
            ist_start, ist_end = s, e
        if city == 'Oslo':
            osl_start, osl_end = s, e
    if not (ist_start <= 5 and ist_end >= 8):
        return False
    if not (osl_start <= 8 and osl_end >= 9):
        return False
    return True

def generate_itinerary():
    for perm in permutations(cities.keys()):
        valid = True
        for i in range(len(perm)-1):
            if perm[i+1] not in flights[perm[i]]:
                valid = False
                break
        if not valid:
            continue
        
        day_ranges = []
        current_day = 1
        for city in perm:
            duration = cities[city]
            end = current_day + duration - 1
            day_ranges.append((current_day, end))
            current_day = end
        
        if check_constraints(day_ranges, perm):
            itinerary = []
            for i, city in enumerate(perm):
                start, end = day_ranges[i]
                day_str = f"Day {start}-{end}" if start != end else f"Day {start}"
                itinerary.append({"day_range": day_str, "place": city})
            return {"itinerary": itinerary}
    return {"itinerary": []}

print(json.dumps(generate_itinerary()))