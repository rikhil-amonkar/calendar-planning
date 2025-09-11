import json
from itertools import permutations

def main():
    cities = ['Paris', 'Florence', 'Vienna', 'Porto', 'Munich', 'Nice', 'Warsaw']
    required_days = {'Paris': 5, 'Florence': 3, 'Vienna': 2, 'Porto': 3, 'Munich': 5, 'Nice': 5, 'Warsaw': 3}
    fixed_events = [
        (1, 3, 'Porto'),
        (13, 15, 'Warsaw'),
        (19, 20, 'Vienna')
    ]
    
    direct_flights = {
        'Florence': ['Vienna', 'Munich', 'Paris'],
        'Paris': ['Warsaw', 'Florence', 'Vienna', 'Nice', 'Munich', 'Porto'],
        'Munich': ['Vienna', 'Florence', 'Warsaw', 'Nice', 'Paris', 'Porto'],
        'Vienna': ['Florence', 'Munich', 'Porto', 'Warsaw', 'Paris', 'Nice'],
        'Porto': ['Vienna', 'Munich', 'Nice', 'Paris', 'Warsaw'],
        'Warsaw': ['Paris', 'Munich', 'Vienna', 'Nice', 'Porto'],
        'Nice': ['Munich', 'Warsaw', 'Vienna', 'Paris', 'Porto']
    }

    def is_valid_flight(from_city, to_city):
        return to_city in direct_flights.get(from_city, [])

    city_list = [city for city in cities if city not in ['Porto', 'Warsaw', 'Vienna']]
    best_itinerary = None
    min_days = float('inf')

    for order in permutations(city_list):
        itinerary = []
        current_day = 1
        days_spent = {city: 0 for city in cities}
        prev_city = 'Porto'
        itinerary.append(('Porto', 1, 3))
        days_spent['Porto'] += 3
        current_day = 4
        valid = True

        for city in order:
            if not is_valid_flight(prev_city, city):
                valid = False
                break
            stay_days = required_days[city]
            itinerary.append((city, current_day, current_day + stay_days - 1))
            days_spent[city] += stay_days
            current_day += stay_days
            prev_city = city

        if not valid:
            continue

        if not is_valid_flight(prev_city, 'Warsaw'):
            continue

        Warsaw_start = current_day
        if Warsaw_start > 13:
            continue
        Warsaw_end = Warsaw_start + required_days['Warsaw'] - 1
        if Warsaw_end < 15:
            continue
        itinerary.append(('Warsaw', Warsaw_start, Warsaw_end))
        days_spent['Warsaw'] += required_days['Warsaw']
        current_day = Warsaw_end + 1

        if not is_valid_flight('Warsaw', 'Vienna'):
            continue

        Vienna_start = current_day
        if Vienna_start > 19:
            continue
        Vienna_end = Vienna_start + required_days['Vienna'] - 1
        if Vienna_end < 20:
            continue
        itinerary.append(('Vienna', Vienna_start, Vienna_end))
        days_spent['Vienna'] += required_days['Vienna']
        current_day = Vienna_end + 1

        if current_day - 1 > 20:
            continue

        for city, req_days in required_days.items():
            if days_spent[city] < req_days:
                valid = False
                break

        if valid and current_day - 1 <= 20:
            if current_day - 1 < min_days:
                min_days = current_day - 1
                best_itinerary = itinerary

    if best_itinerary is None:
        print(json.dumps({"itinerary": []}))
        return

    output_itinerary = []
    for city, start, end in best_itinerary:
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        output_itinerary.append({"day_range": day_range, "place": city})

    print(json.dumps({"itinerary": output_itinerary}))

if __name__ == '__main__':
    main()