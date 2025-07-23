import json
import itertools

def main():
    cities = {
        'Warsaw': 4,
        'Venice': 3,
        'Vilnius': 3,
        'Salzburg': 4,
        'Amsterdam': 2,
        'Barcelona': 5,
        'Paris': 2,
        'Hamburg': 4,
        'Florence': 5,
        'Tallinn': 2
    }
    
    fixed_events = [
        {'place': 'Paris', 'start': 1, 'end': 2},
        {'place': 'Barcelona', 'start': 2, 'end': 6},
        {'place': 'Hamburg', 'start': 19, 'end': 22},
        {'place': 'Salzburg', 'start': 22, 'end': 25}
    ]
    
    direct_flights = {
        'Paris': ['Venice', 'Barcelona', 'Hamburg', 'Vilnius', 'Amsterdam', 'Florence', 'Warsaw', 'Tallinn'],
        'Barcelona': ['Amsterdam', 'Warsaw', 'Hamburg', 'Florence', 'Venice', 'Tallinn'],
        'Amsterdam': ['Barcelona', 'Warsaw', 'Vilnius', 'Hamburg', 'Venice', 'Tallinn'],
        'Warsaw': ['Barcelona', 'Amsterdam', 'Venice', 'Vilnius', 'Hamburg', 'Tallinn'],
        'Venice': ['Paris', 'Barcelona', 'Warsaw', 'Amsterdam', 'Hamburg'],
        'Vilnius': ['Amsterdam', 'Paris', 'Warsaw', 'Tallinn'],
        'Hamburg': ['Barcelona', 'Amsterdam', 'Paris', 'Venice', 'Warsaw', 'Salzburg'],
        'Florence': ['Barcelona', 'Paris', 'Amsterdam'],
        'Tallinn': ['Barcelona', 'Amsterdam', 'Paris', 'Warsaw', 'Vilnius'],
        'Salzburg': ['Hamburg']
    }
    
    flexible_cities = ['Warsaw', 'Venice', 'Vilnius', 'Tallinn', 'Florence', 'Amsterdam']
    city_durations = {city: cities[city] for city in flexible_cities}
    
    for perm in itertools.permutations(flexible_cities):
        if perm[0] not in direct_flights['Barcelona']:
            continue
        if perm[-1] not in direct_flights['Hamburg']:
            continue
            
        valid_order = True
        for i in range(len(perm)-1):
            if perm[i+1] not in direct_flights[perm[i]]:
                valid_order = False
                break
        if not valid_order:
            continue
            
        start_days = {}
        current_start = 7
        for idx, city in enumerate(perm):
            start_days[city] = current_start
            current_start += city_durations[city]
        last_city = perm[-1]
        end_last = start_days[last_city] + city_durations[last_city] - 1
        if end_last > 18:
            continue
            
        tallinn_ok = False
        if 'Tallinn' in perm:
            tallinn_start = start_days['Tallinn']
            tallinn_end = tallinn_start + city_durations['Tallinn'] - 1
            if (tallinn_start <= 11 <= tallinn_end) or (tallinn_start <= 12 <= tallinn_end):
                tallinn_ok = True
            else:
                continue
        else:
            continue
            
        if not tallinn_ok:
            continue
            
        itinerary = []
        itinerary.append({'day_range': f"Day 1-2", 'place': 'Paris'})
        itinerary.append({'day_range': f"Day 2-6", 'place': 'Barcelona'})
        
        for city in perm:
            s = start_days[city]
            e = s + city_durations[city] - 1
            if s == e:
                dr = f"Day {s}"
            else:
                dr = f"Day {s}-{e}"
            itinerary.append({'day_range': dr, 'place': city})
            
        itinerary.append({'day_range': f"Day 19-22", 'place': 'Hamburg'})
        itinerary.append({'day_range': f"Day 22-25", 'place': 'Salzburg'})
        
        print(json.dumps({'itinerary': itinerary}))
        return
        
    print(json.dumps({'itinerary': []}))

if __name__ == '__main__':
    main()