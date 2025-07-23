import json
from itertools import permutations

def find_itinerary():
    cities = {
        'Lisbon': {'duration': 2, 'constraints': [{'range': (4, 5), 'type': 'workshop'}]},
        'Dubrovnik': {'duration': 5, 'constraints': []},
        'Copenhagen': {'duration': 5, 'constraints': []},
        'Prague': {'duration': 3, 'constraints': []},
        'Tallinn': {'duration': 2, 'constraints': [{'range': (1, 2), 'type': 'meet'}]},
        'Stockholm': {'duration': 4, 'constraints': [{'range': (13, 16), 'type': 'wedding'}]},
        'Split': {'duration': 3, 'constraints': []},
        'Lyon': {'duration': 2, 'constraints': [{'range': (18, 19), 'type': 'show'}]}
    }

    direct_flights = {
        'Dubrovnik': ['Stockholm', 'Copenhagen'],
        'Lisbon': ['Copenhagen', 'Lyon', 'Stockholm', 'Prague'],
        'Copenhagen': ['Lisbon', 'Stockholm', 'Split', 'Dubrovnik', 'Prague', 'Tallinn'],
        'Prague': ['Stockholm', 'Lyon', 'Lisbon', 'Split', 'Copenhagen'],
        'Tallinn': ['Stockholm', 'Copenhagen', 'Prague'],
        'Stockholm': ['Dubrovnik', 'Copenhagen', 'Prague', 'Tallinn', 'Lisbon', 'Split'],
        'Split': ['Copenhagen', 'Stockholm', 'Prague', 'Lyon'],
        'Lyon': ['Lisbon', 'Prague', 'Split']
    }

    city_names = list(cities.keys())
    total_days = 19

    def satisfies_constraints(itinerary):
        day_counter = 1
        for entry in itinerary:
            city = entry['place']
            start_day = day_counter
            end_day = day_counter + entry['duration'] - 1
            day_counter = end_day + 1

            for constraint in cities[city]['constraints']:
                c_start, c_end = constraint['range']
                if not (c_start >= start_day and c_end <= end_day):
                    return False

        return day_counter - 1 == total_days

    def is_connected(itinerary):
        for i in range(len(itinerary) - 1):
            current_city = itinerary[i]['place']
            next_city = itinerary[i+1]['place']
            if next_city not in direct_flights[current_city]:
                return False
        return True

    for perm in permutations(cities.items(), len(cities)):
        temp_itinerary = [{'place': city, 'duration': data['duration']} for city, data in perm]
        if is_connected(temp_itinerary) and satisfies_constraints(temp_itinerary):
            final_itinerary = []
            day_counter = 1
            for entry in temp_itinerary:
                start_day = day_counter
                end_day = day_counter + entry['duration'] - 1
                final_itinerary.append({
                    'day_range': f"Day {start_day}-{end_day}",
                    'place': entry['place']
                })
                day_counter = end_day + 1
            return {'itinerary': final_itinerary}

    return {'itinerary': []}

result = find_itinerary()
print(json.dumps(result, indent=2))