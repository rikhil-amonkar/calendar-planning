def build_itinerary(schedule):
    if not schedule:
        return {"itinerary": []}
    
    # Define friends' availability
    friends = {
        'Person A': {'start': 9.0, 'duration': 1.0},
        'Person B': {'start': 9.5, 'duration': 0.5},
        'Person C': {'start': 10.0, 'duration': 1.5},
        'Person D': {'start': 11.0, 'duration': 1.0}
    }
    
    # Define travel times between locations (in hours)
    travel_times = {
        'Marina District': {
            'Golden Gate Park': 15/60,
            'Richmond District': 20/60,
            'Mission District': 25/60
        },
        'Golden Gate Park': {
            'Marina District': 15/60,
            'Richmond District': 9/60,
            'Mission District': 30/60
        },
        'Richmond District': {
            'Marina District': 20/60,
            'Golden Gate Park': 9/60,
            'Mission District': 35/60
        },
        'Mission District': {
            'Marina District': 25/60,
            'Golden Gate Park': 30/60,
            'Richmond District': 35/60
        }
    }
    
    # Helper function to convert float hours to time string
    def float_to_time(time_float):
        hours = int(time_float)
        minutes = int((time_float - hours) * 60)
        return f"{hours:02d}:{minutes:02d}"
    
    itinerary = []
    current_time = 9.0  # Start at 9:00 AM at Marina District
    current_location = 'Marina District'
    
    for meeting in schedule:
        # Get travel time between current location and meeting location
        if current_location == meeting['location']:
            travel_time = 0
        else:
            travel_time = travel_times[current_location][meeting['location']]
        
        arrival_time = current_time + travel_time
        
        # Add travel action if needed
        if travel_time > 0:
            itinerary.append({
                "action": "travel",
                "from": current_location,
                "to": meeting['location'],
                "start_time": float_to_time(current_time),
                "end_time": float_to_time(arrival_time)
            })
        
        # Calculate meeting times - ensure we don't start before friend's availability
        start_time = max(arrival_time, friends[meeting['person']]['start'])
        end_time = start_time + friends[meeting['person']]['duration']
        
        # Add meeting action
        itinerary.append({
            "action": "meet",
            "location": meeting['location'],
            "person": meeting['person'],
            "start_time": float_to_time(start_time),
            "end_time": float_to_time(end_time)
        })
        
        # Update current time and location
        current_time = end_time
        current_location = meeting['location']
    
    return {"itinerary": itinerary}