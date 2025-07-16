import json

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def calculate_schedule():
    # Input parameters
    travel_times = {
        ('North Beach', 'Union Square'): 7,
        ('North Beach', 'Russian Hill'): 4,
        ('Union Square', 'North Beach'): 10,
        ('Union Square', 'Russian Hill'): 13,
        ('Russian Hill', 'North Beach'): 5,
        ('Russian Hill', 'Union Square'): 11
    }
    
    # Constraints
    start_location = 'North Beach'
    start_time = '9:00'
    
    emily_location = 'Union Square'
    emily_window_start = '16:00'
    emily_window_end = '17:15'
    emily_min_duration = 45
    
    margaret_location = 'Russian Hill'
    margaret_window_start = '19:00'
    margaret_window_end = '21:00'
    margaret_min_duration = 120
    
    # Convert all times to minutes
    current_time = time_to_minutes(start_time)
    current_location = start_location
    
    emily_start = time_to_minutes(emily_window_start)
    emily_end = time_to_minutes(emily_window_end)
    margaret_start = time_to_minutes(margaret_window_start)
    margaret_end = time_to_minutes(margaret_window_end)
    
    itinerary = []
    
    # Calculate earliest possible time to meet Emily
    # Option 1: Go directly to Union Square to meet Emily
    travel_to_emily = travel_times[(current_location, emily_location)]
    arrival_at_emily = current_time + travel_to_emily
    
    # Can we meet Emily at her earliest time?
    emily_meeting_start = max(arrival_at_emily, emily_start)
    emily_meeting_end = emily_meeting_start + emily_min_duration
    
    if emily_meeting_end <= emily_end:
        # We can meet Emily, now check if we can meet Margaret
        # Travel from Emily to Margaret
        travel_to_margaret = travel_times[(emily_location, margaret_location)]
        arrival_at_margaret = emily_meeting_end + travel_to_margaret
        
        margaret_meeting_start = max(arrival_at_margaret, margaret_start)
        margaret_meeting_end = margaret_meeting_start + margaret_min_duration
        
        if margaret_meeting_end <= margaret_end:
            # Both meetings possible
            itinerary.append({
                "action": "meet",
                "location": emily_location,
                "person": "Emily",
                "start_time": minutes_to_time(emily_meeting_start),
                "end_time": minutes_to_time(emily_meeting_end)
            })
            itinerary.append({
                "action": "meet",
                "location": margaret_location,
                "person": "Margaret",
                "start_time": minutes_to_time(margaret_meeting_start),
                "end_time": minutes_to_time(margaret_meeting_end)
            })
        else:
            # Only Emily meeting possible
            itinerary.append({
                "action": "meet",
                "location": emily_location,
                "person": "Emily",
                "start_time": minutes_to_time(emily_meeting_start),
                "end_time": minutes_to_time(emily_meeting_end)
            })
    else:
        # Can't meet Emily, try to meet Margaret directly
        travel_to_margaret = travel_times[(current_location, margaret_location)]
        arrival_at_margaret = current_time + travel_to_margaret
        
        margaret_meeting_start = max(arrival_at_margaret, margaret_start)
        margaret_meeting_end = margaret_meeting_start + margaret_min_duration
        
        if margaret_meeting_end <= margaret_end:
            itinerary.append({
                "action": "meet",
                "location": margaret_location,
                "person": "Margaret",
                "start_time": minutes_to_time(margaret_meeting_start),
                "end_time": minutes_to_time(margaret_meeting_end)
            })
    
    return {"itinerary": itinerary}

# Compute and output the schedule
schedule = calculate_schedule()
print(json.dumps(schedule, indent=2))