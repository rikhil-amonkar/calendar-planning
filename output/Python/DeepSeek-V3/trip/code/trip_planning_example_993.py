import json
from itertools import permutations

def find_itinerary():
    # Cities and their required days
    cities = {
        'Riga': 2,
        'Frankfurt': 3,
        'Amsterdam': 2,
        'Vilnius': 5,
        'London': 2,
        'Stockholm': 3,
        'Bucharest': 4
    }
    
    # Direct flights
    direct_flights = {
        'London': ['Amsterdam', 'Bucharest', 'Frankfurt', 'Stockholm'],
        'Amsterdam': ['London', 'Stockholm', 'Frankfurt', 'Riga', 'Bucharest', 'Vilnius'],
        'Vilnius': ['Frankfurt', 'Riga', 'Amsterdam'],
        'Riga': ['Vilnius', 'Stockholm', 'Frankfurt', 'Bucharest', 'Amsterdam'],
        'Frankfurt': ['Vilnius', 'Amsterdam', 'Stockholm', 'Bucharest', 'London', 'Riga'],
        'Stockholm': ['Riga', 'Amsterdam', 'Frankfurt', 'London'],
        'Bucharest': ['London', 'Amsterdam', 'Frankfurt', 'Riga']
    }
    
    # Constraints
    constraints = [
        ('Amsterdam', 2, 3),  # Meet friend between day 2 and 3
        ('Vilnius', 7, 11),   # Workshop between day 7 and 11
        ('Stockholm', 13, 15) # Wedding between day 13 and 15
    ]
    
    # Generate all possible permutations of the cities
    for perm in permutations(cities.keys()):
        itinerary = []
        current_day = 1
        valid = True
        
        # Check if the permutation satisfies all constraints
        for city, days in zip(perm, [cities[c] for c in perm]):
            # Check if current city placement fits constraints
            for const_city, start, end in constraints:
                if city == const_city:
                    if not (current_day <= end and (current_day + days - 1) >= start):
                        valid = False
                        break
            if not valid:
                break
            
            # Add stay
            itinerary.append({
                'day_range': f'Day {current_day}-{current_day + days - 1}',
                'place': city
            })
            
            current_day += days
            
            # Add flight if not last city
            if current_day <= 15 and city != perm[-1]:
                next_city = perm[perm.index(city) + 1]
                if next_city in direct_flights[city]:
                    itinerary.append({
                        'flying': f'Day {current_day}-{current_day}',
                        'from': city,
                        'to': next_city
                    })
                else:
                    valid = False
                    break
        
        if valid and current_day - 1 == 15:
            # Check all constraints again to be sure
            meets_constraints = True
            for const_city, start, end in constraints:
                found = False
                for entry in itinerary:
                    if 'place' in entry and entry['place'] == const_city:
                        day_start = int(entry['day_range'].split('-')[0].split(' ')[1])
                        day_end = int(entry['day_range'].split('-')[1])
                        if (day_start <= end) and (day_end >= start):
                            found = True
                            break
                if not found:
                    meets_constraints = False
                    break
            if meets_constraints:
                return itinerary
    
    return None

itinerary = find_itinerary()
if itinerary:
    print(json.dumps(itinerary, indent=2))
else:
    print(json.dumps({"error": "No valid itinerary found"}, indent=2))