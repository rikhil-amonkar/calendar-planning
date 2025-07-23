import json
from itertools import permutations

def find_itinerary():
    # Define cities and required days
    cities = {
        'Stockholm': 3,
        'Hamburg': 5,
        'Florence': 2,
        'Istanbul': 5,
        'Oslo': 5,
        'Vilnius': 5,
        'Santorini': 2,
        'Munich': 5,
        'Frankfurt': 4,
        'Krakow': 5
    }
    
    # Direct flights
    direct_flights = {
        'Oslo': ['Stockholm', 'Istanbul', 'Krakow', 'Vilnius', 'Frankfurt', 'Hamburg', 'Munich'],
        'Stockholm': ['Oslo', 'Istanbul', 'Munich', 'Hamburg', 'Santorini', 'Krakow', 'Frankfurt'],
        'Krakow': ['Frankfurt', 'Istanbul', 'Vilnius', 'Oslo', 'Munich', 'Stockholm'],
        'Frankfurt': ['Krakow', 'Istanbul', 'Florence', 'Stockholm', 'Munich', 'Hamburg', 'Vilnius'],
        'Istanbul': ['Krakow', 'Oslo', 'Stockholm', 'Vilnius', 'Frankfurt', 'Munich', 'Hamburg'],
        'Vilnius': ['Krakow', 'Istanbul', 'Oslo', 'Frankfurt', 'Munich'],
        'Munich': ['Stockholm', 'Hamburg', 'Istanbul', 'Oslo', 'Frankfurt', 'Florence', 'Krakow', 'Vilnius'],
        'Hamburg': ['Stockholm', 'Munich', 'Istanbul', 'Frankfurt', 'Oslo'],
        'Florence': ['Frankfurt', 'Munich'],
        'Santorini': ['Stockholm', 'Oslo']
    }
    
    # We'll try different starting cities that can reach Krakow
    possible_starts = [city for city in direct_flights['Krakow'] if cities[city] >= 4]
    
    for start_city in possible_starts:
        # Try different permutations of the remaining cities (excluding Istanbul and Krakow)
        other_cities = [city for city in cities if city not in [start_city, 'Krakow', 'Istanbul']]
        
        for perm in permutations(other_cities, len(other_cities)):
            itinerary = []
            current_day = 1
            valid = True
            
            # Start with the starting city (days 1-4)
            itinerary.append({'day_range': 'Day 1-4', 'place': start_city})
            current_day = 5
            
            # Then Krakow for workshop (days 5-9)
            itinerary.append({'day_range': 'Day 5-9', 'place': 'Krakow'})
            current_day = 10
            
            # Now plan the middle part (days 10-24)
            current_city = 'Krakow'
            remaining_cities = {city: cities[city] for city in perm}
            remaining_cities['Istanbul'] = 5  # Istanbul is fixed at the end
            
            temp_itinerary = []
            temp_day = current_day
            
            while temp_day < 25 and remaining_cities:
                # Find next city we can fly to with remaining days
                next_city = None
                for city in remaining_cities:
                    if city in direct_flights[current_city] and remaining_cities[city] > 0:
                        next_city = city
                        break
                
                if not next_city:
                    valid = False
                    break
                
                # Calculate stay duration
                stay_days = min(remaining_cities[next_city], 25 - temp_day)
                if stay_days <= 0:
                    valid = False
                    break
                
                temp_itinerary.append({'day_range': f'Day {temp_day}-{temp_day+stay_days-1}', 'place': next_city})
                remaining_cities[next_city] -= stay_days
                if remaining_cities[next_city] == 0:
                    del remaining_cities[next_city]
                
                temp_day += stay_days
                current_city = next_city
            
            if not valid:
                continue
            
            # Now place Istanbul (days 25-29)
            if 'Istanbul' not in direct_flights[current_city] or temp_day > 25:
                continue
            
            temp_itinerary.append({'day_range': 'Day 25-29', 'place': 'Istanbul'})
            current_day = 30
            current_city = 'Istanbul'
            
            # Check if we have any remaining days (30-32)
            if remaining_cities:
                # Try to fit remaining cities
                for city in list(remaining_cities.keys()):
                    if city in direct_flights[current_city] and remaining_cities[city] <= 3:
                        temp_itinerary.append({'day_range': f'Day {current_day}-{current_day+remaining_cities[city]-1}', 'place': city})
                        current_day += remaining_cities[city]
                        del remaining_cities[city]
            
            if remaining_cities:
                continue
            
            # Combine all parts of the itinerary
            full_itinerary = itinerary + temp_itinerary
            
            # Verify all requirements are met
            day_counts = {city: 0 for city in cities}
            for entry in full_itinerary:
                place = entry['place']
                day_range = entry['day_range']
                start, end = map(int, day_range.split('-')[0][4:], day_range.split('-')[1][4:])
                day_counts[place] += (end - start + 1)
            
            if all(day_counts[city] == cities[city] for city in cities):
                # Verify flight connections
                for i in range(len(full_itinerary)-1):
                    current = full_itinerary[i]['place']
                    next_place = full_itinerary[i+1]['place']
                    if next_place not in direct_flights[current]:
                        valid = False
                        break
                
                if valid:
                    return {'itinerary': full_itinerary}
    
    return {'itinerary': []}

# Run the function and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))