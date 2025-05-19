import json
from itertools import permutations

def main():
    cities = {
        'Reykjavik': {'days': 2, 'event': (3, 4)},
        'Stockholm': {'days': 2, 'event': (4, 5)},
        'Porto': {'days': 5, 'event': (13, 17)},
        'Nice': {'days': 3, 'event': None},
        'Venice': {'days': 4, 'event': None},
        'Vienna': {'days': 3, 'event': (11, 13)},
        'Split': {'days': 3, 'event': None},
        'Copenhagen': {'days': 2, 'event': None}
    }

    flights = {
        'Copenhagen': ['Vienna', 'Split', 'Stockholm', 'Porto', 'Venice', 'Nice'],
        'Nice': ['Stockholm', 'Reykjavik', 'Porto', 'Venice', 'Vienna', 'Copenhagen'],
        'Split': ['Copenhagen', 'Vienna', 'Stockholm'],
        'Reykjavik': ['Nice', 'Vienna', 'Copenhagen', 'Stockholm'],
        'Stockholm': ['Nice', 'Copenhagen', 'Split', 'Vienna', 'Reykjavik'],
        'Venice': ['Nice', 'Vienna', 'Copenhagen'],
        'Vienna': ['Copenhagen', 'Nice', 'Reykjavik', 'Stockholm', 'Venice', 'Porto', 'Split'],
        'Porto': ['Nice', 'Copenhagen', 'Vienna']
    }

    city_names = list(cities.keys())
    for perm in permutations(city_names):
        valid = True
        for i in range(len(perm)-1):
            if perm[i+1] not in flights[perm[i]]:
                valid = False
                break
        if not valid:
            continue

        day = 1
        itinerary = []
        prev_end = 0
        event_checks = {city: False for city, data in cities.items() if data['event']}

        try:
            for city in perm:
                data = cities[city]
                start = day
                if city == 'Reykjavik':
                    if not (start <= 3 and start + data['days'] -1 >=4):
                        start = 3 - data['days'] +1
                elif city == 'Stockholm':
                    if start > 5:
                        raise ValueError
                elif city == 'Vienna':
                    if start > 11 or start + data['days'] -1 < 13:
                        raise ValueError
                elif city == 'Porto':
                    if start >13 or start + data['days'] -1 <17:
                        raise ValueError

                end = start + data['days'] -1
                itinerary.append((start, end, city))
                day = end

                if data['event']:
                    estart, eend = data['event']
                    if not (start <= eend and end >= estart):
                        raise ValueError
                    event_checks[city] = True

            total_days = sum(cities[city]['days'] for city in perm) - (len(perm) -1)
            if total_days !=17:
                continue

            if all(event_checks.values()):
                final_itinerary = []
                for start, end, city in sorted(itinerary, key=lambda x: x[0]):
                    if start == end:
                        dr = f"Day {start}"
                    else:
                        dr = f"Day {start}-{end}"
                    final_itinerary.append({"day_range": dr, "place": city})
                print(json.dumps({"itinerary": final_itinerary}, indent=2))
                return
        except:
            continue

    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()