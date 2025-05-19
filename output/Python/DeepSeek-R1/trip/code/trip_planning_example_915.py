import json
from itertools import permutations

def main():
    cities = {
        'Bucharest': 3,
        'Venice': 5,
        'Prague': 4,
        'Frankfurt': 5,
        'Zurich': 5,
        'Florence': 5,
        'Tallinn': 5
    }
    
    fixed_dates = {
        'Venice': (22, 26),
        'Frankfurt': (12, 16),
        'Tallinn': (8, 12)
    }
    
    flights = {
        'Prague': ['Tallinn', 'Zurich', 'Florence', 'Bucharest', 'Frankfurt'],
        'Tallinn': ['Prague', 'Zurich', 'Frankfurt'],
        'Zurich': ['Prague', 'Bucharest', 'Florence', 'Frankfurt', 'Venice', 'Tallinn'],
        'Florence': ['Prague', 'Frankfurt'],
        'Frankfurt': ['Bucharest', 'Venice', 'Tallinn', 'Zurich', 'Florence', 'Prague'],
        'Bucharest': ['Frankfurt', 'Prague', 'Zurich'],
        'Venice': ['Frankfurt', 'Zurich']
    }

    def is_valid_order(order):
        for i in range(len(order)-1):
            if order[i+1] not in flights[order[i]]:
                return False
        return True

    for perm in permutations(cities.keys()):
        if 'Venice' != perm[-1]:
            continue
        if not is_valid_order(perm):
            continue
        
        timeline = []
        current_day = 1
        req_days = cities.copy()
        date_constraints_met = {city: False for city in fixed_dates}
        
        try:
            for city in perm:
                duration = req_days[city]
                start = current_day
                end = current_day + duration - 1
                
                if city in fixed_dates:
                    req_start, req_end = fixed_dates[city]
                    if not (start <= req_end and end >= req_start):
                        raise ValueError
                    if city == 'Frankfurt' and (start > 12 or end < 16):
                        raise ValueError
                    if city == 'Tallinn' and (start > 8 or end < 12):
                        raise ValueError
                    if city == 'Venice' and (start != 22 or end !=26):
                        raise ValueError
                
                timeline.append({'day_range': f'Day {start}-{end}', 'place': city})
                current_day = end + 1
                
            if current_day -1 != 26:
                continue
                
            for city in cities:
                total = sum(1 for entry in timeline if entry['place'] == city)
                if total != cities[city]:
                    break
            else:
                print(json.dumps({'itinerary': timeline}))
                return
                
        except:
            continue

    print(json.dumps({'itinerary': []}))

if __name__ == "__main__":
    main()