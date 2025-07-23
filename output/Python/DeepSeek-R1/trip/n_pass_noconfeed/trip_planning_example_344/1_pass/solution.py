import itertools
import json

def main():
    total_days = 20
    cities = [
        {'name': 'Valencia', 'days': 6, 'constraint': None},
        {'name': 'Athens', 'days': 6, 'constraint': [1, 6]},
        {'name': 'Naples', 'days': 5, 'constraint': [16, 20]},
        {'name': 'Zurich', 'days': 6, 'constraint': None}
    ]
    
    flights = [
        ('Valencia', 'Naples'),
        ('Valencia', 'Athens'),
        ('Athens', 'Naples'),
        ('Zurich', 'Naples'),
        ('Athens', 'Zurich'),
        ('Zurich', 'Valencia')
    ]
    
    valid_flights = set()
    for a, b in flights:
        if a < b:
            valid_flights.add((a, b))
        else:
            valid_flights.add((b, a))
    
    perms = list(itertools.permutations(cities))
    result = None
    for perm in perms:
        starts = [1]
        for i in range(1, 4):
            s = starts[i-1] + perm[i-1]['days'] - 1
            starts.append(s)
        last_day = starts[3] + perm[3]['days'] - 1
        if last_day != total_days:
            continue
        
        constraints_ok = True
        for i in range(4):
            city = perm[i]
            if city['constraint'] is not None:
                low, high = city['constraint']
                s = starts[i]
                block_end = s + city['days'] - 1
                if not (s <= high and block_end >= low):
                    constraints_ok = False
                    break
        if not constraints_ok:
            continue
        
        flights_ok = True
        for i in range(3):
            city1 = perm[i]['name']
            city2 = perm[i+1]['name']
            if city1 < city2:
                pair = (city1, city2)
            else:
                pair = (city2, city1)
            if pair not in valid_flights:
                flights_ok = False
                break
        if not flights_ok:
            continue
        
        itinerary = []
        for i in range(4):
            start = starts[i]
            end = start + perm[i]['days'] - 1
            day_range_str = f"Day {start}-{end}"
            itinerary.append({
                'day_range': day_range_str,
                'place': perm[i]['name']
            })
        result = {"itinerary": itinerary}
        break
    
    if result is None:
        result = {"error": "No valid itinerary found"}
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()