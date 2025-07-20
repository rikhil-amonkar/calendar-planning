def plan_itinerary(events, travel_matrix, home_city, start_day, end_day):
    # Create a list of unique cities from events
    unique_cities = list(set(event['city'] for event in events))
    
    # Initialize the itinerary as a list of dictionaries
    itinerary = []
    
    # Add home city as the starting point
    itinerary.append({
        'day_range': f"Day {start_day}",
        'place': home_city
    })
    
    # Plan the itinerary based on events
    current_day = start_day
    current_city = home_city
    
    # Process each event in the given order
    for event in events:
        city = event['city']
        event_start = event['start']
        event_end = event['end']
        
        # If the event is in the current city, extend the stay if needed
        if city == current_city:
            # Check if the event is already covered within the current stay
            if current_day <= event_start:
                # Update the end day of the current stay to cover the event
                current_day = event_end + 1  # Stay ends after the event
            else:
                # The event has already passed, move to the next event
                continue
        else:
            # Calculate travel days to the event city
            travel_days = travel_matrix[current_city][city]
            
            # Departure day from current city
            depart_day = current_day
            arrive_day = depart_day + travel_days
            
            # Add travel segment
            itinerary.append({
                'day_range': f"Day {depart_day}",
                'place': f"Travel from {current_city} to {city}"
            })
            
            # Update current city and day
            current_city = city
            current_day = arrive_day
            
            # Ensure we arrive by the event start date
            if current_day > event_start:
                # If we arrive late, we cannot cover the event from the start
                # Adjust by arriving earlier? But we have fixed events before.
                # Since we cannot, we start from the arrival day
                event_start = current_day
            else:
                # We arrive before the event starts, so wait until the event starts
                current_day = event_start
            
            # Add the event city stay
            itinerary.append({
                'day_range': f"Day {current_day}-{event_end}",
                'place': city
            })
            current_day = event_end + 1
    
    # Return home at the end
    travel_days = travel_matrix[current_city][home_city]
    depart_day = current_day
    arrive_home_day = depart_day + travel_days
    if depart_day < end_day:
        itinerary.append({
            'day_range': f"Day {depart_day}",
            'place': f"Travel from {current_city} to {home_city}"
        })
        itinerary.append({
            'day_range': f"Day {arrive_home_day}",
            'place': home_city
        })
    
    return {
        'itinerary': itinerary
    }

# Test data (as provided in the problem)
events = [
    {'city': 'Stockholm', 'start': 0, 'end': 2},
    {'city': 'Amsterdam', 'start': 3, 'end': 4},
    {'city': 'Valencia', 'start': 5, 'end': 5},
    {'city': 'Bucharest', 'start': 6, 'end': 7},
    {'city': 'Vienna', 'start': 8, 'end': 11},
    {'city': 'Reykjavik', 'start': 12, 'end': 15},
    {'city': 'Athens', 'start': 14, 'end': 18},
    {'city': 'Riga', 'start': 20, 'end': 21},
    {'city': 'Frankfurt', 'start': 22, 'end': 24},
    {'city': 'Salzburg', 'start': 25, 'end': 28}
]

travel_matrix = {
    "Stockholm": {"Amsterdam": 1, "Valencia": 2, "Bucharest": 2, "Vienna": 2, "Reykjavik": 2, "Athens": 2, "Riga": 1, "Frankfurt": 2, "Salzburg": 2, "Berlin": 2},
    "Amsterdam": {"Stockholm": 1, "Valencia": 1, "Bucharest": 2, "Vienna": 1, "Reykjavik": 2, "Athens": 2, "Riga": 2, "Frankfurt": 1, "Salzburg": 2, "Berlin": 1},
    "Valencia": {"Stockholm": 2, "Amsterdam": 1, "Bucharest": 2, "Vienna": 2, "Reykjavik": 2, "Athens": 2, "Riga": 2, "Frankfurt": 2, "Salzburg": 2, "Berlin": 2},
    "Bucharest": {"Stockholm": 2, "Amsterdam": 2, "Valencia": 2, "Vienna": 1, "Reykjavik": 2, "Athens": 1, "Riga": 2, "Frankfurt": 2, "Salzburg": 2, "Berlin": 2},
    "Vienna": {"Stockholm": 2, "Amsterdam": 1, "Valencia": 2, "Bucharest": 1, "Reykjavik": 2, "Athens": 1, "Riga": 2, "Frankfurt": 1, "Salzburg": 1, "Berlin": 1},
    "Reykjavik": {"Stockholm": 2, "Amsterdam": 2, "Valencia": 2, "Bucharest": 2, "Vienna": 2, "Athens": 2, "Riga": 2, "Frankfurt": 2, "Salzburg": 2, "Berlin": 2},
    "Athens": {"Stockholm": 2, "Amsterdam": 2, "Valencia": 2, "Bucharest": 1, "Vienna": 1, "Reykjavik": 2, "Riga": 2, "Frankfurt": 2, "Salzburg": 2, "Berlin": 2},
    "Riga": {"Stockholm": 1, "Amsterdam": 2, "Valencia": 2, "Bucharest": 2, "Vienna": 2, "Reykjavik": 2, "Athens": 2, "Frankfurt": 2, "Salzburg": 2, "Berlin": 2},
    "Frankfurt": {"Stockholm": 2, "Amsterdam": 1, "Valencia": 2, "Bucharest": 2, "Vienna": 1, "Reykjavik": 2, "Athens": 2, "Riga": 2, "Salzburg": 1, "Berlin": 1},
    "Salzburg": {"Stockholm": 2, "Amsterdam": 2, "Valencia": 2, "Bucharest": 2, "Vienna": 1, "Reykjavik": 2, "Athens": 2, "Riga": 2, "Frankfurt": 1, "Berlin": 1},
    "Berlin": {"Stockholm": 2, "Amsterdam": 1, "Valencia": 2, "Bucharest": 2, "Vienna": 1, "Reykjavik": 2, "Athens": 2, "Riga": 2, "Frankfurt": 1, "Salzburg": 1}
}

home_city = "Stockholm"
start_day = 0
end_day = 28

# Generate itinerary
result = plan_itinerary(events, travel_matrix, home_city, start_day, end_day)
print(result)