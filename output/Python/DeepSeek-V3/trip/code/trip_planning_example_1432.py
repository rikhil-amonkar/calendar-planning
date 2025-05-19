import json
from itertools import permutations

def main():
    # Input parameters
    total_days = 29
    cities = {
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
    constraints = [
        {'city': 'Athens', 'day_range': (14, 18)},
        {'city': 'Valencia', 'day_range': (5, 6)},
        {'city': 'Vienna', 'day_range': (6, 10)},
        {'city': 'Stockholm', 'day_range': (1, 3)},
        {'city': 'Riga', 'day_range': (18, 20)}
    ]
    
    # Direct flights
    direct_flights = {
        'Valencia': ['Frankfurt', 'Athens', 'Bucharest', 'Vienna', 'Amsterdam'],
        'Vienna': ['Bucharest', 'Riga', 'Frankfurt', 'Athens', 'Stockholm', 'Amsterdam', 'Reykjavik', 'Valencia'],
        'Athens': ['Valencia', 'Bucharest', 'Riga', 'Frankfurt', 'Stockholm', 'Vienna', 'Amsterdam', 'Reykjavik'],
        'Riga': ['Frankfurt', 'Bucharest', 'Vienna', 'Amsterdam', 'Stockholm', 'Athens'],
        'Stockholm': ['Athens', 'Vienna', 'Amsterdam', 'Riga', 'Frankfurt', 'Reykjavik'],
        'Amsterdam': ['Bucharest', 'Frankfurt', 'Reykjavik', 'Stockholm', 'Valencia', 'Vienna', 'Riga', 'Athens'],
        'Frankfurt': ['Valencia', 'Riga', 'Amsterdam', 'Salzburg', 'Vienna', 'Bucharest', 'Stockholm', 'Athens', 'Reykjavik'],
        'Bucharest': ['Vienna', 'Athens', 'Amsterdam', 'Valencia', 'Frankfurt', 'Riga'],
        'Reykjavik': ['Amsterdam', 'Frankfurt', 'Athens', 'Stockholm', 'Vienna'],
        'Salzburg': ['Frankfurt']
    }
    
    # Pre-process constraints to assign mandatory days
    mandatory_days = {}
    for day in range(1, total_days + 1):
        mandatory_days[day] = None
    for constraint in constraints:
        start, end = constraint['day_range']
        for day in range(start, end + 1):
            mandatory_days[day] = constraint['city']
    
    # Assign remaining days to cities
    remaining_cities = {city: duration for city, duration in cities.items()}
    for day, city in mandatory_days.items():
        if city is not None:
            remaining_cities[city] -= 1
    
    # Generate all possible city orders that satisfy constraints
    city_list = list(remaining_cities.keys())
    possible_orders = permutations(city_list)
    
    # Find a valid itinerary
    itinerary = []
    for order in possible_orders:
        temp_itinerary = []
        current_city = None
        remaining_days = remaining_cities.copy()
        day = 1
        valid = True
        
        while day <= total_days:
            if mandatory_days[day] is not None:
                city = mandatory_days[day]
                if current_city == city:
                    pass
                elif current_city is None or city in direct_flights[current_city]:
                    if current_city is not None:
                        temp_itinerary.append({'flying': f'Day {day}-{day}', 'from': current_city, 'to': city})
                    current_city = city
                else:
                    valid = False
                    break
                remaining_days[city] -= 1
                day += 1
            else:
                if current_city is None:
                    # Start with Stockholm (since it has day 1-3 constraint)
                    current_city = 'Stockholm'
                    temp_itinerary.append({'day_range': f'Day {day}-{day + remaining_days[current_city] - 1}', 'place': current_city})
                    day += remaining_days[current_city]
                    remaining_days[current_city] = 0
                else:
                    found = False
                    for city in order:
                        if remaining_days[city] > 0 and city in direct_flights[current_city]:
                            temp_itinerary.append({'flying': f'Day {day}-{day}', 'from': current_city, 'to': city})
                            current_city = city
                            stay_days = remaining_days[city]
                            temp_itinerary.append({'day_range': f'Day {day + 1}-{day + stay_days}', 'place': city})
                            day += stay_days + 1
                            remaining_days[city] = 0
                            found = True
                            break
                    if not found:
                        valid = False
                        break
        
        if valid and all(v == 0 for v in remaining_days.values()):
            itinerary = temp_itinerary
            break
    
    # Post-process to merge consecutive stays and add mandatory days
    final_itinerary = []
    i = 0
    while i < len(itinerary):
        entry = itinerary[i]
        if 'place' in entry:
            start_day = int(entry['day_range'].split('-')[0].split(' ')[1])
            end_day = int(entry['day_range'].split('-')[1])
            place = entry['place']
            # Check if next entries are the same place
            while i + 1 < len(itinerary) and 'place' in itinerary[i+1] and itinerary[i+1]['place'] == place:
                next_entry = itinerary[i+1]
                next_end_day = int(next_entry['day_range'].split('-')[1])
                end_day = next_end_day
                i += 1
            final_itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': place})
        else:
            final_itinerary.append(entry)
        i += 1
    
    print(json.dumps(final_itinerary, indent=2))

if __name__ == "__main__":
    main()