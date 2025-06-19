def create_itinerary(events):
    # Sort events by start date and then by end date to ensure chronological processing
    events_sorted = sorted(events, key=lambda x: (x['start'], x['end']))
    
    # Create a list to hold the itinerary
    itinerary = []
    current_day = 1
    last_city = None
    
    # Process each event to generate continuous stays
    for event in events_sorted:
        city = event['city']
        start = event['start']
        end = event['end']
        
        # If there's a gap between current_day and the event start, we need to fill it
        if current_day < start:
            # This should not happen if events are contiguous, but handle for safety
            gap_start = current_day
            gap_end = start - 1
            if last_city is not None:
                itinerary.append({
                    'day_range': f'Day {gap_start}-{gap_end}',
                    'place': last_city
                })
            current_day = start
        
        # If switching cities, add the transition at the start date
        if last_city is not None and last_city != city:
            itinerary.append({
                'day_range': f'Day {start}',
                'place': last_city
            })
            itinerary.append({
                'day_range': f'Day {start}',
                'place': city
            })
        
        # Add the continuous stay for the event duration
        itinerary.append({
            'day_range': f'Day {start}-{end}',
            'place': city
        })
        
        # Add the last day of the event explicitly for clarity
        itinerary.append({
            'day_range': f'Day {end}',
            'place': city
        })
        
        current_day = end + 1
        last_city = city
    
    # If there are remaining days after the last event, extend the stay in the last city
    if current_day <= 22:
        itinerary.append({
            'day_range': f'Day {current_day}-22',
            'place': last_city
        })
    
    return {'itinerary': itinerary}

events = [
    {'city': 'Mykonos', 'start': 1, 'end': 3},
    {'city': 'Nice', 'start': 3, 'end': 4},
    {'city': 'Riga', 'start': 4, 'end': 6},  # Adjusted to end on day 6
    {'city': 'Prague', 'start': 7, 'end': 9},
    {'city': 'Bucharest', 'start': 10, 'end': 14},
    {'city': 'Zurich', 'start': 14, 'end': 18},
    {'city': 'Valencia', 'start': 18, 'end': 22}
]

itinerary = create_itinerary(events)
print(itinerary)