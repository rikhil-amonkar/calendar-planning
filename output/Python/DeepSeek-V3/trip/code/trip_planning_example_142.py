import json

def calculate_itinerary():
    # Input parameters
    total_days = 7
    madrid_days = 4
    dublin_days = 3
    tallinn_days = 2
    tallinn_workshop_start = 6
    tallinn_workshop_end = 7
    
    # Direct flight connections
    direct_flights = {
        'Madrid': ['Dublin'],
        'Dublin': ['Madrid', 'Tallinn'],
        'Tallinn': ['Dublin']
    }
    
    # Validate the days sum
    if madrid_days + dublin_days + tallinn_days != total_days:
        raise ValueError("Total days in cities do not match the trip duration")
    
    # Determine possible sequences based on flight connections
    possible_sequences = []
    
    # Option 1: Madrid -> Dublin -> Tallinn
    if 'Dublin' in direct_flights['Madrid'] and 'Tallinn' in direct_flights['Dublin']:
        possible_sequences.append(['Madrid', 'Dublin', 'Tallinn'])
    
    # Option 2: Dublin -> Madrid -> Dublin -> Tallinn
    if 'Madrid' in direct_flights['Dublin'] and 'Dublin' in direct_flights['Tallinn']:
        possible_sequences.append(['Dublin', 'Madrid', 'Dublin', 'Tallinn'])
    
    # Find a sequence that fits the days and workshop constraint
    valid_itinerary = None
    
    for sequence in possible_sequences:
        # Calculate day allocations
        current_day = 1
        itinerary = []
        prev_city = None
        
        for city in sequence:
            if prev_city is not None and prev_city != city:
                itinerary.append({
                    'flying': f'Day {current_day}-{current_day}',
                    'from': prev_city,
                    'to': city
                })
                current_day += 0  # Assuming flight doesn't take a full day
            
            if city == 'Madrid':
                end_day = current_day + madrid_days - 1
                itinerary.append({
                    'day_range': f'Day {current_day}-{end_day}',
                    'place': 'Madrid'
                })
                current_day = end_day + 1
            elif city == 'Dublin':
                end_day = current_day + dublin_days - 1
                itinerary.append({
                    'day_range': f'Day {current_day}-{end_day}',
                    'place': 'Dublin'
                })
                current_day = end_day + 1
            elif city == 'Tallinn':
                end_day = current_day + tallinn_days - 1
                itinerary.append({
                    'day_range': f'Day {current_day}-{end_day}',
                    'place': 'Tallinn'
                })
                current_day = end_day + 1
            
            prev_city = city
        
        # Check if Tallinn is visited during workshop days
        tallinn_visit = [item for item in itinerary if item.get('place') == 'Tallinn']
        if tallinn_visit:
            tallinn_range = tallinn_visit[0]['day_range']
            start, end = map(int, tallinn_range.replace('Day ', '').split('-'))
            if start <= tallinn_workshop_start and end >= tallinn_workshop_end:
                valid_itinerary = itinerary
                break
    
    if not valid_itinerary:
        raise ValueError("No valid itinerary found that satisfies all constraints")
    
    return valid_itinerary

# Compute and output the itinerary
itinerary = calculate_itinerary()
print(json.dumps(itinerary, indent=2))