import json
from itertools import permutations

def find_valid_itinerary():
    cities = {
        'Reykjavik': 7,
        'Riga': 2,
        'Warsaw': 3,
        'Istanbul': 6,
        'Krakow': 7
    }
    
    direct_flights = {
        'Istanbul': ['Krakow', 'Warsaw', 'Riga'],
        'Krakow': ['Istanbul', 'Warsaw'],
        'Warsaw': ['Istanbul', 'Krakow', 'Reykjavik', 'Riga'],
        'Riga': ['Istanbul', 'Warsaw'],
        'Reykjavik': ['Warsaw']
    }
    
    constraints = {
        'Riga': {'meet_friend': (1, 2)},
        'Istanbul': {'wedding': (2, 7)}
    }
    
    city_names = list(cities.keys())
    
    for perm in permutations(city_names):
        itinerary = list(perm)
        valid = True
        
        for i in range(len(itinerary) - 1):
            current = itinerary[i]
            next_city = itinerary[i + 1]
            if next_city not in direct_flights.get(current, []):
                valid = False
                break
        
        if not valid:
            continue
        
        day = 1
        plan = []
        meets_constraints = True
        
        for city in itinerary:
            duration = cities[city]
            plan.append({
                'day_range': f'Day {day}-{day + duration - 1}',
                'place': city
            })
            
            if city == 'Riga':
                meet_start, meet_end = constraints['Riga']['meet_friend']
                if not (day <= meet_start <= day + duration - 1 and day <= meet_end <= day + duration - 1):
                    meets_constraints = False
                    break
            
            if city == 'Istanbul':
                wedding_start, wedding_end = constraints['Istanbul']['wedding']
                if not (day <= wedding_start <= day + duration - 1 and day <= wedding_end <= day + duration - 1):
                    meets_constraints = False
                    break
            
            day += duration
            
            if city != itinerary[-1]:
                next_city = itinerary[itinerary.index(city) + 1]
                plan.append({
                    'flying': f'Day {day}-{day}',
                    'from': city,
                    'to': next_city
                })
                day += 1
        
        if meets_constraints and day - 1 == 21:
            return plan
    
    return None

def main():
    itinerary = find_valid_itinerary()
    if itinerary:
        print(json.dumps(itinerary, indent=2))
    else:
        print(json.dumps({"error": "No valid itinerary found"}, indent=2))

if __name__ == "__main__":
    main()