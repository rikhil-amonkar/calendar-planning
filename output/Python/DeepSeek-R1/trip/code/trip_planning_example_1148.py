import json
from itertools import permutations

def main():
    cities = {
        'Tallinn': {'days': 2, 'constraints': [(1, 2)]},
        'Lisbon': {'days': 2, 'constraints': [(4, 5)]},
        'Dubrovnik': {'days': 5},
        'Copenhagen': {'days': 5},
        'Prague': {'days': 3},
        'Stockholm': {'days': 4, 'constraints': [(13, 16)]},
        'Split': {'days': 3},
        'Lyon': {'days': 2, 'constraints': [(18, 19)]}
    }

    flights = {
        'Dubrovnik': ['Stockholm', 'Copenhagen'],
        'Lisbon': ['Copenhagen', 'Lyon', 'Stockholm', 'Prague'],
        'Copenhagen': ['Dubrovnik', 'Stockholm', 'Split', 'Prague', 'Tallinn', 'Lisbon'],
        'Prague': ['Stockholm', 'Lyon', 'Lisbon', 'Split', 'Copenhagen'],
        'Tallinn': ['Stockholm', 'Copenhagen', 'Prague'],
        'Stockholm': ['Dubrovnik', 'Copenhagen', 'Prague', 'Tallinn', 'Lisbon', 'Split'],
        'Split': ['Copenhagen', 'Stockholm', 'Prague', 'Lyon'],
        'Lyon': ['Lisbon', 'Prague', 'Split']
    }

    city_names = list(cities.keys())

    for perm in permutations(city_names):
        valid = True
        day = 1
        itinerary = []
        prev_city = None
        
        for city in perm:
            req_days = cities[city]['days']
            cons = cities[city].get('constraints', [])
            start = day
            end = day + req_days - 1
            
            if prev_city and city not in flights[prev_city]:
                valid = False
                break
            
            for (s, e) in cons:
                if not (s >= start and e <= end):
                    valid = False
                    break
            if not valid:
                break
            
            if city == 'Tallinn':
                if not (start <= 1 and end >= 2):
                    valid = False
                    break
            elif city == 'Lyon':
                if end < 18:
                    valid = False
                    break
            elif city == 'Stockholm':
                if not (start <= 13 and end >= 16):
                    valid = False
                    break
            elif city == 'Lisbon':
                if not (start <= 4 and end >= 5):
                    valid = False
                    break
            
            itinerary.append({'day_range': f"Day {start}-{end}", 'place': city})
            day += req_days
            prev_city = city
            
            if day > 19:
                valid = False
                break
        
        if valid and day - 1 == 19:
            print(json.dumps({'itinerary': itinerary}))
            return
    
    print(json.dumps({'itinerary': []}))

if __name__ == "__main__":
    main()