import json

def calculate_itinerary():
    # Input parameters
    total_days = 15
    stuttgart_days = 6
    seville_days = 7
    manchester_days = 4
    
    # Direct flights
    direct_flights = {
        'Manchester': ['Seville'],
        'Seville': ['Manchester'],
        'Stuttgart': ['Manchester'],
        'Manchester': ['Stuttgart']
    }
    
    # Cities to visit
    cities = {
        'Stuttgart': stuttgart_days,
        'Seville': seville_days,
        'Manchester': manchester_days
    }
    
    # Determine possible sequences based on direct flights
    possible_sequences = []
    
    # Option 1: Stuttgart -> Manchester -> Seville
    if 'Manchester' in direct_flights['Stuttgart'] and 'Seville' in direct_flights['Manchester']:
        possible_sequences.append(['Stuttgart', 'Manchester', 'Seville'])
    
    # Option 2: Stuttgart -> Seville -> Manchester (not possible, no direct flight)
    # Option 3: Manchester -> Stuttgart -> Seville
    if 'Stuttgart' in direct_flights['Manchester'] and 'Seville' in direct_flights['Stuttgart']:
        possible_sequences.append(['Manchester', 'Stuttgart', 'Seville'])
    # But Stuttgart doesn't have direct flight to Seville, so this is invalid
    
    # Option 4: Manchester -> Seville -> Stuttgart
    if 'Seville' in direct_flights['Manchester'] and 'Stuttgart' in direct_flights['Seville']:
        possible_sequences.append(['Manchester', 'Seville', 'Stuttgart'])
    # Seville doesn't have direct flight to Stuttgart, so invalid
    
    # Option 5: Seville -> Manchester -> Stuttgart
    if 'Manchester' in direct_flights['Seville'] and 'Stuttgart' in direct_flights['Manchester']:
        possible_sequences.append(['Seville', 'Manchester', 'Stuttgart'])
    
    # The only valid sequences are Option 1 and Option 5
    valid_sequences = []
    for seq in possible_sequences:
        if len(seq) == 3:
            valid_sequences.append(seq)
    
    # Choose the first valid sequence (both are equivalent in terms of days)
    if not valid_sequences:
        raise ValueError("No valid itinerary found with given constraints")
    
    chosen_sequence = valid_sequences[0]
    
    # Build itinerary
    itinerary = []
    current_day = 1
    
    # First city
    first_city = chosen_sequence[0]
    first_days = cities[first_city]
    itinerary.append({
        'day_range': f'Day {current_day}-{current_day + first_days - 1}',
        'place': first_city
    })
    current_day += first_days
    
    # Flight to second city
    second_city = chosen_sequence[1]
    itinerary.append({
        'flying': f'Day {current_day}-{current_day}',
        'from': first_city,
        'to': second_city
    })
    
    # Second city
    second_days = cities[second_city]
    itinerary.append({
        'day_range': f'Day {current_day + 1}-{current_day + second_days}',
        'place': second_city
    })
    current_day += second_days + 1
    
    # Flight to third city
    third_city = chosen_sequence[2]
    itinerary.append({
        'flying': f'Day {current_day}-{current_day}',
        'from': second_city,
        'to': third_city
    })
    
    # Third city
    third_days = cities[third_city]
    itinerary.append({
        'day_range': f'Day {current_day + 1}-{current_day + third_days}',
        'place': third_city
    })
    
    return itinerary

def main():
    itinerary = calculate_itinerary()
    print(json.dumps(itinerary, indent=2))

if __name__ == "__main__":
    main()