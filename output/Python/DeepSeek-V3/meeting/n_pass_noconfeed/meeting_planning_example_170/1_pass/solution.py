import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(dt):
    return dt.strftime("%-H:%M")

def calculate_schedule():
    # Input parameters
    travel_times = {
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Russian Hill"): 4,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Russian Hill"): 13,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Union Square"): 11
    }
    
    # Constraints
    current_location = "North Beach"
    current_time = parse_time("9:00")
    
    emily_location = "Union Square"
    emily_window_start = parse_time("16:00")
    emily_window_end = parse_time("17:15")
    emily_min_duration = 45  # minutes
    
    margaret_location = "Russian Hill"
    margaret_window_start = parse_time("19:00")
    margaret_window_end = parse_time("21:00")
    margaret_min_duration = 120  # minutes
    
    itinerary = []
    
    # First, try to meet Emily
    # Calculate travel time to Emily
    travel_to_emily = travel_times[(current_location, emily_location)]
    earliest_arrival_emily = current_time + timedelta(minutes=travel_to_emily)
    
    # Find the latest possible start time for Emily meeting
    latest_emily_start = emily_window_end - timedelta(minutes=emily_min_duration)
    
    # Determine when we can meet Emily
    emily_meeting_start = max(earliest_arrival_emily, emily_window_start)
    if emily_meeting_start <= latest_emily_start:
        emily_meeting_end = emily_meeting_start + timedelta(minutes=emily_min_duration)
        itinerary.append({
            "action": "meet",
            "location": emily_location,
            "person": "Emily",
            "start_time": format_time(emily_meeting_start),
            "end_time": format_time(emily_meeting_end)
        })
        current_location = emily_location
        current_time = emily_meeting_end
    
    # Then try to meet Margaret
    # Calculate travel time to Margaret
    travel_to_margaret = travel_times[(current_location, margaret_location)]
    earliest_arrival_margaret = current_time + timedelta(minutes=travel_to_margaret)
    
    # Find the latest possible start time for Margaret meeting
    latest_margaret_start = margaret_window_end - timedelta(minutes=margaret_min_duration)
    
    # Determine when we can meet Margaret
    margaret_meeting_start = max(earliest_arrival_margaret, margaret_window_start)
    if margaret_meeting_start <= latest_margaret_start:
        margaret_meeting_end = margaret_meeting_start + timedelta(minutes=margaret_min_duration)
        itinerary.append({
            "action": "meet",
            "location": margaret_location,
            "person": "Margaret",
            "start_time": format_time(margaret_meeting_start),
            "end_time": format_time(margaret_meeting_end)
        })
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))