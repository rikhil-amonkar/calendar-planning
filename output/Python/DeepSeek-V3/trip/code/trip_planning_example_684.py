import json
from itertools import permutations

def find_valid_itinerary():
    cities = {
        'Amsterdam': {'duration': 4, 'constraints': [(5, 8)]},
        'Edinburgh': {'duration': 5, 'constraints': []},
        'Brussels': {'duration': 5, 'constraints': []},
        'Vienna': {'duration': 5, 'constraints': []},
        'Berlin': {'duration': 4, 'constraints': [(16, 19)]},
        'Reykjavik': {'duration': 5, 'constraints': [(12, 16)]}
    }
    
    direct_flights = {
        'Edinburgh': ['Berlin', 'Amsterdam', 'Brussels'],
        'Amsterdam': ['Berlin', 'Edinburgh', 'Reykjavik', 'Vienna'],
        'Vienna': ['Berlin', 'Brussels', 'Reykjavik', 'Amsterdam'],
        'Berlin': ['Edinburgh', 'Amsterdam', 'Vienna', 'Brussels', 'Reykjavik'],
        'Brussels': ['Berlin', 'Edinburgh', 'Vienna', 'Reykjavik'],
        'Reykjavik': ['Vienna', 'Amsterdam', 'Brussels', 'Berlin']
    }
    
    total_days = 23
    city_names = list(cities.keys())
    
    for perm in permutations(city_names):
        itinerary = []
        current_day = 1
        valid = True
        
        for i, city in enumerate(perm):
            duration = cities[city]['duration']
            end_day = current_day + duration - 1
            
            if end_day > total_days:
                valid = False
                break
            
            # Check constraints
            for (start_con, end_con) in cities[city]['constraints']:
                if not (current_day <= start_con and end_day >= end_con):
                    valid = False
                    break
            if not valid:
                break
            
            itinerary.append((current_day, end_day, city))
            
            if i < len(perm) - 1:
                next_city = perm[i+1]
                if next_city not in direct_flights[city]:
                    valid = False
                    break
                current_day = end_day + 1
        
        if valid and len(itinerary) == len(city_names):
            return itinerary
    
    return None

def format_itinerary(itinerary):
    formatted = []
    for i, (start, end, city) in enumerate(itinerary):
        day_range = f"Day {start}-{end}"
        formatted.append({'day_range': day_range, 'place': city})
        if i < len(itinerary) - 1:
            next_city = itinerary[i+1][2]
            formatted.append({'flying': f"Day {end}-{end}", 'from': city, 'to': next_city})
    return formatted

def main():
    itinerary = find_valid_itinerary()
    if itinerary:
        formatted = format_itinerary(itinerary)
        print(json.dumps(formatted, indent=2))
    else:
        print(json.dumps({"error": "No valid itinerary found"}, indent=2))

if __name__ == "__main__":
    main()