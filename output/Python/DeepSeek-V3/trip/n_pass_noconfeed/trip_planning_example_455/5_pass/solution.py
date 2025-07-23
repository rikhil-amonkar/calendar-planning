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
    
    # Generate all possible permutations of cities that respect flight connections
    def generate_valid_sequences(current_sequence, remaining_cities, sequences):
        if not remaining_cities:
            sequences.append(current_sequence)
            return
        
        last_city = current_sequence[-1] if current_sequence else None
        
        for city in remaining_cities:
            if not last_city or city in flight_connections[last_city]:
                new_remaining = remaining_cities.copy()
                new_remaining.remove(city)
                generate_valid_sequences(current_sequence + [city], new_remaining, sequences)
    
    sequences = []
    generate_valid_sequences([], list(cities.keys()), sequences)
    
    # Try to find a valid itinerary
    for sequence in sequences:
        # Create day assignments
        day_assignments = {}
        used_days = set()
        
        # Assign Riga first (must be days 1-2)
        riga_days = cities['Riga']
        riga_start = constraints['Riga'][0]
        riga_end = riga_start + riga_days - 1
        if riga_end > constraints['Riga'][1]:
            continue  # Can't fit Riga in required window
        
        day_assignments['Riga'] = (riga_start, riga_end)
        used_days.update(range(riga_start, riga_end + 1))
        
        # Assign Istanbul next (must be days 2-7)
        istanbul_days = cities['Istanbul']
        # Find earliest possible start that doesn't conflict with Riga
        istanbul_start = max(2, riga_end + 1)
        istanbul_end = istanbul_start + istanbul_days - 1
        
        if istanbul_end > constraints['Istanbul'][1]:
            continue  # Can't fit Istanbul in required window
        
        day_assignments['Istanbul'] = (istanbul_start, istanbul_end)
        used_days.update(range(istanbul_start, istanbul_end + 1))
        
        # Assign remaining cities in sequence
        remaining_cities = [city for city in sequence if city not in ['Riga', 'Istanbul']]
        current_day = 1
        valid = True
        
        for city in remaining_cities:
            days_needed = cities[city]
            
            # Find earliest contiguous block of available days
            available_days = sorted(set(range(1, total_days + 1)) - used_days)
            
            # Find first block that fits
            start_day = None
            for day in available_days:
                end_day = day + days_needed - 1
                if end_day > total_days:
                    continue
                if all(d not in used_days for d in range(day, end_day + 1)):
                    start_day = day
                    break
            
            if start_day is None:
                valid = False
                break
            
            end_day = start_day + days_needed - 1
            day_assignments[city] = (start_day, end_day)
            used_days.update(range(start_day, end_day + 1))
        
        if valid and len(day_assignments) == len(cities):
            # Create ordered itinerary
            itinerary = []
            for day in range(1, total_days + 1):
                for city, (start, end) in day_assignments.items():
                    if start <= day <= end:
                        itinerary.append({
                            'day': day,
                            'place': city
                        })
                        break
            
            # Group consecutive days in the same city
            grouped_itinerary = []
            current_entry = None
            for entry in itinerary:
                if current_entry and current_entry['place'] == entry['place']:
                    current_entry['end_day'] = entry['day']
                else:
                    if current_entry:
                        grouped_itinerary.append(current_entry)
                    current_entry = {
                        'start_day': entry['day'],
                        'end_day': entry['day'],
                        'place': entry['place']
                    }
            if current_entry:
                grouped_itinerary.append(current_entry)
            
            # Format the output
            formatted_itinerary = []
            for entry in grouped_itinerary:
                if entry['start_day'] == entry['end_day']:
                    day_range = f"Day {entry['start_day']}"
                else:
                    day_range = f"Day {entry['start_day']}-{entry['end_day']}"
                formatted_itinerary.append({
                    'day_range': day_range,
                    'place': entry['place']
                })
            
            return {'itinerary': formatted_itinerary}
    
    return {'itinerary': []}

result = calculate_itinerary()
print(json.dumps(result, indent=2))