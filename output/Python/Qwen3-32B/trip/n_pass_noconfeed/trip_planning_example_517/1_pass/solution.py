import itertools
import json

def main():
    cities = ['Dubrovnik', 'Warsaw', 'Stuttgart', 'Bucharest', 'Copenhagen']
    durations = {
        'Dubrovnik': 5,
        'Warsaw': 2,
        'Stuttgart': 7,
        'Bucharest': 6,
        'Copenhagen': 3
    }
    allowed_flights = {
        ('Warsaw', 'Copenhagen'),
        ('Copenhagen', 'Warsaw'),
        ('Stuttgart', 'Copenhagen'),
        ('Copenhagen', 'Stuttgart'),
        ('Warsaw', 'Stuttgart'),
        ('Stuttgart', 'Warsaw'),
        ('Bucharest', 'Copenhagen'),
        ('Copenhagen', 'Bucharest'),
        ('Bucharest', 'Warsaw'),
        ('Warsaw', 'Bucharest'),
        ('Copenhagen', 'Dubrovnik'),
        ('Dubrovnik', 'Copenhagen'),
    }

    for perm in itertools.permutations(cities):
        valid_transitions = True
        for i in range(len(perm) - 1):
            if (perm[i], perm[i + 1]) not in allowed_flights:
                valid_transitions = False
                break
        if not valid_transitions:
            continue

        start_day = 1
        stuttgart_start = None
        bucharest_start = None
        city_days = []
        for city in perm:
            dur = durations[city]
            end_day = start_day + dur - 1
            if city == 'Stuttgart':
                stuttgart_start = start_day
            if city == 'Bucharest':
                bucharest_start = start_day
            city_days.append((start_day, end_day, city))
            start_day = end_day

        if stuttgart_start == 7 and bucharest_start is not None and bucharest_start <= 6:
            itinerary = []
            for start, end, city in city_days:
                itinerary.append({
                    "day_range": f"Day {start}-{end}",
                    "place": city
                })
            print(json.dumps({"itinerary": itinerary}))
            return

if __name__ == "__main__":
    main()