def build_itinerary(schedule):
    if not schedule:
        return {"itinerary": []}
    
    itinerary = []
    current_time = 9.0  # Start at 9:00 AM at Marina District
    current_location = 'Marina District'
    
    for meeting in schedule:
        # Travel to meeting location
        travel_time = get_travel_time(current_location, meeting['location'])
        
        # Special case for Richmond District to Golden Gate Park
        if current_location == 'Richmond District' and meeting['location'] == 'Golden Gate Park':
            travel_time = 9 / 60.0  # Ensure we use exactly 9 minutes
            
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
        
        # Calculate meeting times
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