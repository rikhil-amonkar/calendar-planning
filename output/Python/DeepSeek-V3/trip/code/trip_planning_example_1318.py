import json
from itertools import permutations

def find_itinerary():
    # Input parameters
    total_days = 25
    cities = {
        'Oslo': 2,
        'Helsinki': 2,  # Note: Typo in city name (should be Helsinki)
        'Edinburgh': 3,
        'Riga': 2,
        'Tallinn': 5,
        'Budapest': 5,
        'Vilnius': 5,
        'Porto': 5,
        'Geneva': 4
    }
    
    # Correcting the typo in city name
    cities['Helsinki'] = cities.pop('Helsinki')
    
    # Special constraints
    oslo_meetup_day = (24, 25)
    tallinn_wedding = (4, 8)
    
    # Direct flights (undirected graph)
    direct_flights = {
        'Porto': ['Oslo', 'Edinburgh', 'Geneva'],
        'Edinburgh': ['Porto', 'Budapest', 'Geneva', 'Oslo', 'Helsinki', 'Riga'],
        'Riga': ['Tallinn', 'Oslo', 'Helsinki', 'Vilnius', 'Edinburgh'],
        'Tallinn': ['Riga', 'Vilnius', 'Helsinki', 'Oslo'],
        'Vilnius': ['Helsinki', 'Tallinn', 'Oslo', 'Riga'],
        'Helsinki': ['Vilnius', 'Budapest', 'Oslo', 'Geneva', 'Tallinn', 'Edinburgh', 'Riga'],
        'Budapest': ['Edinburgh', 'Geneva', 'Helsinki', 'Oslo'],
        'Geneva': ['Edinburgh', 'Porto', 'Oslo', 'Budapest', 'Helsinki'],
        'Oslo': ['Porto', 'Riga', 'Geneva', 'Edinburgh', 'Vilnius', 'Budapest', 'Helsinki', 'Tallinn']
    }
    
    # Generate all possible city orders that satisfy constraints
    city_names = list(cities.keys())
    
    # We'll try permutations until we find a valid itinerary
    for perm in permutations(city_names):
        itinerary = []
        current_day = 1
        valid = True
        
        # Check if Tallinn is visited during wedding days
        tallinn_pos = perm.index('Tallinn')
        prev_cities = perm[:tallinn_pos]
        days_before_tallinn = sum(cities[city] for city in prev_cities) + len(prev_cities) - 1
        
        tallinn_start = days_before_tallinn + 1
        tallinn_end = tallinn_start + cities['Tallinn'] - 1
        
        if not (tallinn_start <= tallinn_wedding[1] and tallinn_end >= tallinn_wedding[0]):
            continue
        
        # Check Oslo meetup
        oslo_pos = perm.index('Oslo')
        prev_cities = perm[:oslo_pos]
        days_before_oslo = sum(cities[city] for city in prev_cities) + len(prev_cities) - 1
        
        oslo_start = days_before_oslo + 1
        oslo_end = oslo_start + cities['Oslo'] - 1
        
        if not (oslo_start <= oslo_meetup_day[1] and oslo_end >= oslo_meetup_day[0]):
            continue
        
        # Check flight connections
        for i in range(len(perm)):
            if i > 0:
                from_city = perm[i-1]
                to_city = perm[i]
                if to_city not in direct_flights[from_city]:
                    valid = False
                    break
                
                # Add flight day
                itinerary.append({
                    'flying': f'Day {current_day}-{current_day}',
                    'from': from_city,
                    'to': to_city
                })
                current_day += 1
            
            # Add stay
            city = perm[i]
            stay_days = cities[city]
            itinerary.append({
                'day_range': f'Day {current_day}-{current_day + stay_days - 1}',
                'place': city
            })
            current_day += stay_days
        
        if valid and current_day - 1 == total_days:
            return itinerary
    
    return None

def main():
    itinerary = find_itinerary()
    if itinerary:
        print(json.dumps(itinerary, indent=2))
    else:
        print(json.dumps({"error": "No valid itinerary found"}, indent=2))

if __name__ == "__main__":
    main()