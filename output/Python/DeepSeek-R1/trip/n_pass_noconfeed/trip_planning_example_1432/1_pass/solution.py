import itertools
import json

def main():
    cities_duration = {
        'Frankfurt': 4,
        'Salzburg': 5,
        'Athens': 5,
        'Reykjavik': 5,
        'Bucharest': 3,
        'Valencia': 2,
        'Vienna': 5,
        'Amsterdam': 3,
        'Stockholm': 3,
        'Riga': 3
    }
    
    direct_flights = [
        ('Valencia', 'Frankfurt'),
        ('Vienna', 'Bucharest'),
        ('Valencia', 'Athens'),
        ('Athens', 'Bucharest'),
        ('Riga', 'Frankfurt'),
        ('Stockholm', 'Athens'),
        ('Amsterdam', 'Bucharest'),
        ('Athens', 'Riga'),
        ('Amsterdam', 'Frankfurt'),
        ('Stockholm', 'Vienna'),
        ('Vienna', 'Riga'),
        ('Amsterdam', 'Reykjavik'),
        ('Reykjavik', 'Frankfurt'),
        ('Stockholm', 'Amsterdam'),
        ('Amsterdam', 'Valencia'),
        ('Vienna', 'Frankfurt'),
        ('Valencia', 'Bucharest'),
        ('Bucharest', 'Frankfurt'),
        ('Stockholm', 'Frankfurt'),
        ('Valencia', 'Vienna'),
        ('Reykjavik', 'Athens'),
        ('Frankfurt', 'Salzburg'),
        ('Amsterdam', 'Vienna'),
        ('Stockholm', 'Reykjavik'),
        ('Amsterdam', 'Riga'),
        ('Stockholm', 'Riga'),
        ('Vienna', 'Reykjavik'),
        ('Amsterdam', 'Athens'),
        ('Athens', 'Frankfurt'),
        ('Vienna', 'Athens'),
        ('Riga', 'Bucharest')
    ]
    
    flight_set = set()
    for u, v in direct_flights:
        flight_set.add((u, v))
        flight_set.add((v, u))
    
    cities = list(cities_duration.keys())
    found_itinerary = None
    
    for perm in itertools.permutations(cities):
        valid_permutation = True
        for i in range(len(perm)-1):
            if (perm[i], perm[i+1]) not in flight_set:
                valid_permutation = False
                break
        if not valid_permutation:
            continue
        
        start_day = {}
        end_day = {}
        current_start = 1
        for idx, city in enumerate(perm):
            duration = cities_duration[city]
            start_day[city] = current_start
            end_day[city] = current_start + duration - 1
            if idx < len(perm) - 1:
                current_start = end_day[city]
        
        if not (start_day['Valencia'] <= 5 and end_day['Valencia'] >= 6):
            continue
        if not (start_day['Vienna'] <= 10 and end_day['Vienna'] >= 6):
            continue
        if not (start_day['Athens'] <= 18 and end_day['Athens'] >= 14):
            continue
        if not (start_day['Riga'] <= 20 and end_day['Riga'] >= 18):
            continue
        if not (start_day['Stockholm'] <= 3 and end_day['Stockholm'] >= 1):
            continue
        
        itinerary = []
        for city in perm:
            s = start_day[city]
            e = end_day[city]
            if s == e:
                day_str = f"Day {s}"
            else:
                day_str = f"Day {s}-{e}"
            itinerary.append({"day_range": day_str, "place": city})
        found_itinerary = itinerary
        break
    
    if found_itinerary is None:
        result = {"itinerary": []}
    else:
        result = {"itinerary": found_itinerary}
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()