import json

def calculate_itinerary():
    # Input parameters
    total_days = 12
    riga_days = 5
    vilnius_days = 7
    dublin_days = 2
    
    # Validate total days
    if riga_days + vilnius_days + dublin_days != total_days:
        raise ValueError("Total days do not match the sum of individual city days")
    
    # Flight connections
    connections = {
        'Dublin': ['Riga'],
        'Riga': ['Vilnius', 'Dublin'],
        'Vilnius': ['Riga']
    }
    
    # Determine possible sequences
    possible_sequences = []
    
    # Option 1: Dublin -> Riga -> Vilnius
    if 'Dublin' in connections['Riga'] and 'Riga' in connections['Vilnius']:
        possible_sequences.append(['Dublin', 'Riga', 'Vilnius'])
    
    # Option 2: Riga -> Dublin -> Riga -> Vilnius (but this would require revisiting Riga)
    # Not optimal given the constraints, so we'll ignore
    
    # Select the first valid sequence (only one in this case)
    if not possible_sequences:
        raise ValueError("No valid flight sequence found for the given cities")
    
    selected_sequence = possible_sequences[0]
    
    # Build itinerary
    itinerary = []
    current_day = 1
    
    for i, city in enumerate(selected_sequence):
        if city == 'Dublin':
            stay_days = dublin_days
        elif city == 'Riga':
            stay_days = riga_days
        elif city == 'Vilnius':
            stay_days = vilnius_days
        
        # Add stay entry
        end_day = current_day + stay_days - 1
        itinerary.append({
            'day_range': f'Day {current_day}-{end_day}',
            'place': city
        })
        
        # Add flight entry if not last city
        if i < len(selected_sequence) - 1:
            next_city = selected_sequence[i+1]
            itinerary.append({
                'flying': f'Day {end_day}-{end_day}',
                'from': city,
                'to': next_city
            })
            current_day = end_day + 1
    
    return itinerary

if __name__ == "__main__":
    itinerary = calculate_itinerary()
    print(json.dumps(itinerary, indent=2))