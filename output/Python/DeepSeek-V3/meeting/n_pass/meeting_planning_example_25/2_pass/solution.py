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
    
    # Calculate earliest possible meeting time with David
    earliest_meet_start = max(david_start_min, arrival_min + travel_time)
    
    # Calculate meeting end time
    meet_end_time = earliest_meet_start + meet_duration
    if meet_end_time > david_end_min:
        meet_end_time = david_end_min
        meet_duration = meet_end_time - earliest_meet_start
    
    # Build itinerary
    itinerary = []
    
    # Time at Golden Gate Park before meeting David
    if arrival_min < earliest_meet_start - travel_time:
        itinerary.append({
            "action": "stay",
            "location": "Golden Gate Park",
            "person": None,
            "start_time": minutes_to_time(arrival_min),
            "end_time": minutes_to_time(earliest_meet_start - travel_time)
        })
    
    # Travel to Chinatown
    itinerary.append({
        "action": "travel",
        "location": "Golden Gate Park to Chinatown",
        "person": None,
        "start_time": minutes_to_time(earliest_meet_start - travel_time),
        "end_time": minutes_to_time(earliest_meet_start)
    })
    
    # Meeting with David
    itinerary.append({
        "action": "meet",
        "location": "Chinatown",
        "person": "David",
        "start_time": minutes_to_time(earliest_meet_start),
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