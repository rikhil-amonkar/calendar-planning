import json

def calculate_itinerary():
    # Input parameters
    total_days = 15
    cities = {
        'Paris': 6,
        'Madrid': 7,
        'Bucharest': 2,
        'Seville': 3
    }
    
    # Constraints
    madrid_show_days = (1, 7)
    bucharest_relatives_days = (14, 15)
    
    # Direct flights
    direct_flights = {
        'Paris': ['Bucharest', 'Seville', 'Madrid'],
        'Madrid': ['Bucharest', 'Paris', 'Seville'],
        'Bucharest': ['Paris', 'Madrid'],
        'Seville': ['Paris', 'Madrid']
    }
    
    # Initialize itinerary
    itinerary = []
    
    # Assign Madrid first due to the show constraint (Day 1-7)
    current_day = 1
    madrid_days = min(7, cities['Madrid'])
    itinerary.append({
        'day_range': f'Day {current_day}-{current_day + madrid_days - 1}',
        'place': 'Madrid'
    })
    current_day += madrid_days
    cities['Madrid'] -= madrid_days
    
    # Next, assign Bucharest for relatives (Day 14-15)
    # We need to reach Bucharest by Day 14
    remaining_days_before_bucharest = 14 - current_day
    
    # Assign other cities before Bucharest
    remaining_cities = {city: days for city, days in cities.items() if days > 0 and city != 'Bucharest'}
    
    # Try to assign Paris and Seville before Bucharest
    while remaining_days_before_bucharest > 0 and sum(remaining_cities.values()) > 0:
        for city in list(remaining_cities.keys()):
            if remaining_cities[city] > 0:
                # Check if we can fly from Madrid to this city
                if 'Madrid' in direct_flights and city in direct_flights['Madrid']:
                    max_days = min(remaining_cities[city], remaining_days_before_bucharest)
                    if max_days > 0:
                        itinerary.append({
                            'flying': f'Day {current_day}-{current_day}',
                            'from': 'Madrid',
                            'to': city
                        })
                        itinerary.append({
                            'day_range': f'Day {current_day + 1}-{current_day + max_days}',
                            'place': city
                        })
                        current_day += max_days + 1
                        remaining_cities[city] -= max_days
                        remaining_days_before_bucharest = 14 - current_day
    
    # Assign Bucharest for relatives (Day 14-15)
    if cities['Bucharest'] > 0:
        # Find the last city before Bucharest
        last_city = itinerary[-1]['place'] if itinerary and 'place' in itinerary[-1] else 'Madrid'
        if 'Bucharest' in direct_flights.get(last_city, []):
            itinerary.append({
                'flying': f'Day {14 - cities["Bucharest"]}-{14 - cities["Bucharest"]}',
                'from': last_city,
                'to': 'Bucharest'
            })
            itinerary.append({
                'day_range': f'Day {14 - cities["Bucharest"] + 1}-15',
                'place': 'Bucharest'
            })
    
    # After Bucharest, check if there are remaining days for other cities
    # But in this case, all days should be allocated
    
    # Verify all cities are visited with correct days
    # If not, adjust (this is a simplified approach)
    
    # Final check to ensure all days are allocated
    # This is a simplified solution and may need more complex logic for all cases
    
    return itinerary

itinerary = calculate_itinerary()
print(json.dumps(itinerary, indent=2))