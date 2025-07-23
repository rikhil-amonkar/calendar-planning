import json
from itertools import permutations

def calculate_itinerary():
    cities = {
        'Reykjavik': 7,
        'Riga': 2,
        'Warsaw': 3,
        'Istanbul': 6,
        'Krakow': 7
    }
    
    flight_connections = {
        'Istanbul': ['Krakow', 'Warsaw', 'Riga'],
        'Krakow': ['Istanbul', 'Warsaw'],
        'Warsaw': ['Istanbul', 'Krakow', 'Reykjavik', 'Riga'],
        'Riga': ['Istanbul', 'Warsaw'],
        'Reykjavik': ['Warsaw']
    }
    
    total_days = 21
    constraints = {
        'Riga': (1, 2),    # Must be in Riga between day 1-2
        'Istanbul': (2, 7)  # Must be in Istanbul between day 2-7
    }
    
    # Generate all possible city orders that satisfy flight connections
    city_names = list(cities.keys())
    
    # We'll use a recursive approach to build valid sequences
    def build_sequences(current_sequence, remaining_cities, sequences):
        if not remaining_cities:
            sequences.append(current_sequence)
            return
        
        last_city = current_sequence[-1] if current_sequence else None
        
        for city in remaining_cities:
            if not last_city or city in flight_connections[last_city]:
                new_remaining = remaining_cities.copy()
                new_remaining.remove(city)
                build_sequences(current_sequence + [city], new_remaining, sequences)
    
    sequences = []
    build_sequences([], city_names.copy(), sequences)
    
    valid_itineraries = []
    
    for sequence in sequences:
        # Create a day assignment dictionary
        day_assignments = {}
        remaining_days = set(range(1, total_days + 1))
        
        # First assign constrained cities
        # Assign Riga (must be days 1-2)
        if 'Riga' not in sequence:
            continue
        
        riga_days = cities['Riga']
        riga_start = constraints['Riga'][0]
        riga_end = riga_start + riga_days - 1
        if riga_end > constraints['Riga'][1]:
            continue  # Can't fit Riga in required window
        
        day_assignments['Riga'] = (riga_start, riga_end)
        for day in range(riga_start, riga_end + 1):
            if day not in remaining_days:
                break
            remaining_days.remove(day)
        else:
            # Assign Istanbul (must be days 2-7)
            if 'Istanbul' not in sequence:
                continue
            
            istanbul_days = cities['Istanbul']
            # Istanbul must start on or after day 2 and end by day 7
            possible_starts = [d for d in remaining_days 
                             if d >= 2 
                             and d + istanbul_days - 1 <= 7
                             and d + istanbul_days - 1 <= total_days]
            
            for start in possible_starts:
                end = start + istanbul_days - 1
                days_needed = set(range(start, end + 1))
                if days_needed.issubset(remaining_days):
                    day_assignments['Istanbul'] = (start, end)
                    remaining_days -= days_needed
                    break
            else:
                continue  # Couldn't assign Istanbul
            
            # Now assign remaining cities in sequence
            current_sequence = [city for city in sequence if city not in ['Riga', 'Istanbul']]
            current_day = 1
            
            for city in current_sequence:
                if city in day_assignments:
                    continue
                
                days_needed = cities[city]
                # Find earliest contiguous block of days_needed days
                possible_start = None
                consecutive = 0
                
                for day in sorted(remaining_days):
                    if day == current_day + consecutive:
                        consecutive += 1
                        if consecutive == days_needed:
                            possible_start = day - days_needed + 1
                            break
                    else:
                        consecutive = 1
                        current_day = day
                
                if possible_start is None:
                    break  # Can't assign this city
                
                end_day = possible_start + days_needed - 1
                day_assignments[city] = (possible_start, end_day)
                for day in range(possible_start, end_day + 1):
                    remaining_days.remove(day)
            
            if len(day_assignments) == len(cities):
                # Create ordered itinerary
                itinerary = []
                for day in range(1, total_days + 1):
                    for city, (start, end) in day_assignments.items():
                        if start <= day <= end:
                            itinerary.append({
                                'day': f"Day {day}",
                                'place': city
                            })
                            break
                
                # Group consecutive days in the same city
                grouped_itinerary = []
                current_entry = None
                for entry in itinerary:
                    if current_entry and current_entry['place'] == entry['place']:
                        start_day = current_entry['day_range'].split('-')[0].split(' ')[1]
                        end_day = entry['day'].split(' ')[1]
                        current_entry['day_range'] = f"Day {start_day}-{end_day}"
                    else:
                        if current_entry:
                            grouped_itinerary.append(current_entry)
                        current_entry = {
                            'day_range': entry['day'] + '-' + entry['day'].split(' ')[1],
                            'place': entry['place']
                        }
                if current_entry:
                    grouped_itinerary.append(current_entry)
                
                valid_itineraries.append(grouped_itinerary)
    
    if valid_itineraries:
        # Return the first valid itinerary
        return {'itinerary': valid_itineraries[0]}
    else:
        return {'itinerary': []}

result = calculate_itinerary()
print(json.dumps(result, indent=2))