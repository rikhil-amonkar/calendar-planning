import json

def calculate_optimal_schedule():
    # Input parameters
    arrival_time = "9:00"
    david_available_start = "16:00"
    david_available_end = "21:45"
    meet_duration = 105  # minutes
    travel_time = 23  # minutes
    
    # Convert time strings to minutes since midnight
    def time_to_minutes(time_str):
        h, m = map(int, time_str.split(':'))
        return h * 60 + m
    
    arrival_min = time_to_minutes(arrival_time)
    david_start_min = time_to_minutes(david_available_start)
    david_end_min = time_to_minutes(david_available_end)
    
    # Calculate latest possible start time for meeting David
    latest_start_time = david_end_min - meet_duration
    if latest_start_time < david_start_min:
        latest_start_time = david_start_min
    
    # Calculate when to leave Golden Gate Park to meet David
    leave_ggp_time = latest_start_time - travel_time
    
    # Check if we have time to do anything before leaving
    itinerary = []
    
    # Add initial time at Golden Gate Park if there's any
    if arrival_min < leave_ggp_time:
        itinerary.append({
            "action": "stay",
            "location": "Golden Gate Park",
            "person": None,
            "start_time": minutes_to_time(arrival_min),
            "end_time": minutes_to_time(leave_ggp_time)
        })
    
    # Add travel to Chinatown
    itinerary.append({
        "action": "travel",
        "location": "Golden Gate Park to Chinatown",
        "person": None,
        "start_time": minutes_to_time(leave_ggp_time),
        "end_time": minutes_to_time(leave_ggp_time + travel_time)
    })
    
    # Add meeting with David
    meet_end_time = min(latest_start_time + meet_duration, david_end_min)
    itinerary.append({
        "action": "meet",
        "location": "Chinatown",
        "person": "David",
        "start_time": minutes_to_time(latest_start_time),
        "end_time": minutes_to_time(meet_end_time)
    })
    
    return {"itinerary": itinerary}

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

if __name__ == "__main__":
    schedule = calculate_optimal_schedule()
    print(json.dumps(schedule, indent=2))