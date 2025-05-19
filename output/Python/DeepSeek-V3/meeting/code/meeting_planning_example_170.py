import json

def calculate_optimal_schedule():
    # Input parameters
    travel_times = {
        ('North Beach', 'Union Square'): 7,
        ('North Beach', 'Russian Hill'): 4,
        ('Union Square', 'North Beach'): 10,
        ('Union Square', 'Russian Hill'): 13,
        ('Russian Hill', 'North Beach'): 5,
        ('Russian Hill', 'Union Square'): 11
    }
    
    # Initial conditions
    current_location = 'North Beach'
    current_time = 9 * 60  # 9:00 AM in minutes
    
    # Friend constraints
    emily_location = 'Union Square'
    emily_start = 16 * 60  # 4:00 PM
    emily_end = 17 * 60 + 15  # 5:15 PM
    emily_min_duration = 45
    
    margaret_location = 'Russian Hill'
    margaret_start = 19 * 60  # 7:00 PM
    margaret_end = 21 * 60  # 9:00 PM
    margaret_min_duration = 120
    
    itinerary = []
    
    # First, try to meet Emily
    # Calculate travel time to Emily
    travel_to_emily = travel_times[(current_location, emily_location)]
    arrival_at_emily = current_time + travel_to_emily
    
    # Check if we can meet Emily
    if arrival_at_emily <= emily_end - emily_min_duration:
        meet_emily_start = max(arrival_at_emily, emily_start)
        meet_emily_end = meet_emily_start + emily_min_duration
        if meet_emily_end <= emily_end:
            itinerary.append({
                "action": "meet",
                "location": emily_location,
                "person": "Emily",
                "start_time": f"{meet_emily_start // 60}:{meet_emily_start % 60:02d}",
                "end_time": f"{meet_emily_end // 60}:{meet_emily_end % 60:02d}"
            })
            current_location = emily_location
            current_time = meet_emily_end
    
    # Then try to meet Margaret
    # Calculate travel time to Margaret
    travel_to_margaret = travel_times[(current_location, margaret_location)]
    arrival_at_margaret = current_time + travel_to_margaret
    
    # Check if we can meet Margaret
    if arrival_at_margaret <= margaret_end - margaret_min_duration:
        meet_margaret_start = max(arrival_at_margaret, margaret_start)
        meet_margaret_end = meet_margaret_start + margaret_min_duration
        if meet_margaret_end <= margaret_end:
            itinerary.append({
                "action": "meet",
                "location": margaret_location,
                "person": "Margaret",
                "start_time": f"{meet_margaret_start // 60}:{meet_margaret_start % 60:02d}",
                "end_time": f"{meet_margaret_end // 60}:{meet_margaret_end % 60:02d}"
            })
    
    # If we couldn't meet both, try to meet just Margaret
    if not itinerary:
        # Reset to initial conditions
        current_location = 'North Beach'
        current_time = 9 * 60
        
        # Calculate travel time to Margaret
        travel_to_margaret = travel_times[(current_location, margaret_location)]
        arrival_at_margaret = current_time + travel_to_margaret
        
        # Check if we can meet Margaret
        if arrival_at_margaret <= margaret_end - margaret_min_duration:
            meet_margaret_start = max(arrival_at_margaret, margaret_start)
            meet_margaret_end = meet_margaret_start + margaret_min_duration
            if meet_margaret_end <= margaret_end:
                itinerary.append({
                    "action": "meet",
                    "location": margaret_location,
                    "person": "Margaret",
                    "start_time": f"{meet_margaret_start // 60}:{meet_margaret_start % 60:02d}",
                    "end_time": f"{meet_margaret_end // 60}:{meet_margaret_end % 60:02d}"
                })
    
    return {"itinerary": itinerary}

result = calculate_optimal_schedule()
print(json.dumps(result, indent=2))