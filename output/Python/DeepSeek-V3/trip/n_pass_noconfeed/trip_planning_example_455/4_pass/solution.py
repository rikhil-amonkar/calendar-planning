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
    
    # Generate all possible permutations of cities
    city_names = list(cities.keys())
    
    # We'll use a recursive approach to build valid sequences based on flight connections
    def build_sequences(current_sequence, remaining_cities, sequences):
        if not remaining_cities:
            sequences.append(current_sequence)
            return
        
        last_city = current_sequence[-1] if current_sequence else None
        
        for city in remaining_cities:
            if not last_city or city in flight_connections.get(last_city, []):
                new_remaining = remaining_cities.copy()
                new_remaining.remove(city)
                build_sequences(current_sequence + [city], new_remaining, sequences)
    
    sequences = []
    build_sequences([], city_names.copy(), sequences)
    
    valid_itineraries = []
    
    for sequence in sequences:
        # Create a day assignment dictionary
        day_assignments = {}
        used_days = set()
        
        # Assign Riga first (must be days 1-2)
        if 'Riga' not in sequence:
            continue
        
        riga_days = cities['Riga']
        riga_start = constraints['Riga'][0]
        riga_end = riga_start + riga_days - 1
        if riga_end > constraints['Riga'][1]:
            continue  # Can't fit Riga in required window
        
        day_assignments['Riga'] = (riga_start, riga_end)
        used_days.update(range(riga_start, riga_end + 1))
        
        # Assign Istanbul next (must be days 2-7)
        if 'Istanbul' not in sequence:
            continue
        
        istanbul_days = cities['Istanbul']
        # Istanbul must start on or after day 2 and end by day 7
        possible_starts = [d for d in range(2, 8) 
                         if d + istanbul_days - 1 <= 7
                         and not any(day in used_days for day in range(d, d + istanbul_days))]
        
        if not possible_starts:
            continue
        
        # Try to assign Istanbul as early as possible
        istanbul_start = min(possible_starts)
        istanbul_end = istanbul_start + istanbul_days - 1
        day_assignments['Istanbul'] = (istanbul_start, istanbul_end)
        used_days.update(range(istanbul_start, istanbul_end + 1))
        
        # Assign remaining cities in sequence
        current_sequence = [city for city in sequence if city not in ['Riga', 'Istanbul']]
        current_day = 1
        
        for city in current_sequence:
            if city in day_assignments:
                continue
            
            days_needed = cities[city]
            # Find earliest contiguous block of available days
            available_days = sorted(set(range(1, total_days + 1)) - used_days)
            
            # Find the first block of consecutive days that fits
            start_day = None
            consecutive = 0
            
            for day in available_days:
                if consecutive == 0:
                    start_day = day
                    consecutive = 1
                else:
                    if day == start_day + consecutive:
                        consecutive += 1
                    else:
                        start_day = day
                        consecutive = 1
                
                if consecutive == days_needed:
                    break
            
            if consecutive < days_needed:
                break  # Can't assign this city
            
            end_day = start_day + days_needed - 1
            day_assignments[city] = (start_day, end_day)
            used_days.update(range(start_day, end_day + 1))
        
        if len(day_assignments) == len(cities):
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
            
            valid_itineraries.append(formatted_itinerary)
    
    if valid_itineraries:
        # Return the first valid itinerary
        return {'itinerary': valid_itineraries[0]}
    else:
        return {'itinerary': []}

result = calculate_itinerary()
print(json.dumps(result, indent=2))