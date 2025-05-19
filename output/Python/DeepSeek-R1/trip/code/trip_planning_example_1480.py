import json
from itertools import permutations

def main():
    cities = {
        'Geneva': {'days': 4, 'start': 1, 'end': 4},
        'Venice': {'days': 5, 'start': 7, 'end': 11},
        'Vilnius': {'days': 4, 'start': 20, 'end': 23},
        'Brussels': {'days': 2, 'start': 26, 'end': 27},
        'Istanbul': {'days': 4},
        'Vienna': {'days': 4},
        'Riga': {'days': 2},
        'Madrid': {'days': 4},
        'Munich': {'days': 5},
        'Reykjavik': {'days': 2}
    }

    flight_graph = {
        'Geneva': ['Istanbul', 'Vienna', 'Brussels', 'Madrid', 'Munich'],
        'Munich': ['Vienna', 'Istanbul', 'Madrid', 'Venice', 'Reykjavik', 'Riga', 'Brussels', 'Vilnius'],
        'Vienna': ['Munich', 'Vilnius', 'Istanbul', 'Riga', 'Venice', 'Brussels', 'Reykjavik', 'Geneva'],
        'Istanbul': ['Brussels', 'Geneva', 'Vienna', 'Riga', 'Venice', 'Vilnius', 'Madrid', 'Munich'],
        'Brussels': ['Istanbul', 'Venice', 'Riga', 'Vilnius', 'Reykjavik', 'Vienna', 'Madrid', 'Geneva', 'Munich'],
        'Madrid': ['Munich', 'Venice', 'Vienna', 'Brussels', 'Istanbul', 'Geneva', 'Reykjavik'],
        'Venice': ['Brussels', 'Munich', 'Madrid', 'Vienna', 'Istanbul'],
        'Riga': ['Brussels', 'Istanbul', 'Vienna', 'Munich', 'Vilnius'],
        'Vilnius': ['Brussels', 'Istanbul', 'Vienna', 'Munich', 'Riga'],
        'Reykjavik': ['Madrid', 'Vienna', 'Brussels', 'Munich']
    }

    city_names = list(cities.keys())
    city_names.remove('Geneva')
    city_names.remove('Brussels')

    for perm in permutations(city_names):
        path = ['Geneva'] + list(perm) + ['Brussels']
        valid = True
        for i in range(len(path)-1):
            if path[i+1] not in flight_graph.get(path[i], []):
                valid = False
                break
        if not valid:
            continue
        
        current_day = 1
        itinerary = []
        try:
            for i, city in enumerate(path):
                info = cities[city]
                if city == 'Geneva':
                    start = 1
                    end = 4
                else:
                    start = current_day
                    end = start + info['days'] - 1
                    if 'start' in info and (start > info['start'] or end < info['end']):
                        raise ValueError
                    if 'start' in info and 'end' in info:
                        if not (info['start'] <= start <= info['end'] and info['start'] <= end <= info['end']):
                            raise ValueError
                itinerary.append({'start': start, 'end': end, 'name': city})
                current_day = end
                if current_day > 27:
                    break
            if itinerary[-1]['end'] != 27 or itinerary[-1]['name'] != 'Brussels':
                continue
            if len({city['name'] for city in itinerary}) != 10:
                continue
            output = []
            for entry in itinerary:
                if entry['start'] == entry['end']:
                    day_range = f"Day {entry['start']}"
                else:
                    day_range = f"Day {entry['start']}-{entry['end']}"
                output.append({'day_range': day_range, 'place': entry['name']})
            print(json.dumps({'itinerary': output}))
            return
        except:
            continue

    print(json.dumps({'itinerary': []}))

if __name__ == "__main__":
    main()