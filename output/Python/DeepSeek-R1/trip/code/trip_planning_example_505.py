import itertools
import json

cities = ['Prague', 'Stuttgart', 'Split', 'Krakow', 'Florence']
durations = {
    'Prague': 4,
    'Stuttgart': 2,
    'Split': 2,
    'Krakow': 2,
    'Florence': 2
}

flights = {
    'Stuttgart': {'Split', 'Krakow'},
    'Prague': {'Florence', 'Split', 'Krakow'},
    'Split': {'Stuttgart', 'Prague', 'Krakow'},
    'Krakow': {'Stuttgart', 'Split', 'Prague'},
    'Florence': {'Prague'}
}

def generate_itinerary():
    for perm in itertools.permutations(cities):
        valid_flight = True
        for i in range(len(perm)-1):
            if perm[i+1] not in flights[perm[i]]:
                valid_flight = False
                break
        if not valid_flight:
            continue
        
        current_day = 1
        itinerary = []
        valid_days = True
        for city in perm:
            duration = durations[city]
            end_day = current_day + duration - 1
            if end_day > 8:
                valid_days = False
                break
            itinerary.append({'start': current_day, 'end': end_day, 'place': city})
            current_day = end_day
        
        if not valid_days or current_day != 8:
            continue
        
        stuttgart_ok = False
        split_ok = False
        for entry in itinerary:
            s, e, place = entry['start'], entry['end'], entry['place']
            if place == 'Stuttgart' and s <= 2 and e >= 3:
                stuttgart_ok = True
            if place == 'Split' and s <= 3 and e >= 4:
                split_ok = True
        
        if stuttgart_ok and split_ok:
            result = {'itinerary': []}
            for entry in itinerary:
                s = entry['start']
                e = entry['end']
                day_range = f"Day {s}-{e}" if s != e else f"Day {s}"
                result['itinerary'].append({'day_range': day_range, 'place': entry['place']})
            
            counts = {city: 0 for city in cities}
            for entry in result['itinerary']:
                s, e = map(int, entry['day_range'].replace('Day ', '').split('-') if '-' in entry['day_range'] else (int(entry['day_range'].replace('Day ', '')), int(entry['day_range'].replace('Day ', '')))
                counts[entry['place']] += e - s + 1
            
            if all(counts[city] == durations[city] for city in cities):
                return result
    
    return {'itinerary': []}

print(json.dumps(generate_itinerary()))