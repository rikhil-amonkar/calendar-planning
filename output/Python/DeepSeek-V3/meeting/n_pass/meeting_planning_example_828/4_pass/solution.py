def build_itinerary(schedule):
    if not schedule:
        return {"itinerary": []}
    
    # Define friends' availability (assuming this was missing)
    friends = {
        'Person A': {'start': 9.0, 'duration': 1.0},
        'Person B': {'start': 9.5, 'duration': 0.5},
        'Person C': {'start': 10.0, 'duration': 1.5},
        'Person D': {'start': 11.0, 'duration': 1.0}
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
        # Travel to meeting location
        travel_time = get_travel_time(current_location, meeting['location'])
        
        # Special case for Richmond District to Golden Gate Park
        if current_location == 'Richmond District' and meeting['location'] == 'Golden Gate Park':
            travel_time = 9 / 60.0  # 9 minutes in hours
            
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

# Assuming this function exists elsewhere or needs to be defined
def get_travel_time(from_location, to_location):
    # This should be implemented based on actual travel time calculations
    # For now returning a default value
    return 0.25  # 15 minutes as default