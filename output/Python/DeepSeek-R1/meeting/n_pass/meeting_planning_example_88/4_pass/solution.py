import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minutes = int(parts[1]) if len(parts) > 1 else 0
    return hour * 60 + minutes

def minutes_to_time(mins):
    hour = mins // 60
    minutes = mins % 60
    return f"{hour}:{minutes:02d}"

def main():
    # Input parameters
    start_location = "Sunset District"
    start_time_str = "9:00"
    joshua_location = "Golden Gate Park"
    joshua_person = "Joshua"
    joshua_available_start_str = "20:45"
    joshua_available_end_str = "21:45"
    min_meeting_duration = 15
    travel_time_to_ggp = 11  # Sunset District to Golden Gate Park

    # Convert times to minutes
    start_minutes = time_to_minutes(start_time_str)
    joshua_start_minutes = time_to_minutes(joshua_available_start_str)
    joshua_end_minutes = time_to_minutes(joshua_available_end_str)
    
    # Calculate earliest possible arrival time at Golden Gate Park
    earliest_arrival = start_minutes + travel_time_to_ggp
    
    # Determine valid meeting window that satisfies:
    # 1. Within Joshua's availability
    # 2. After earliest possible arrival
    meeting_window_start = max(earliest_arrival, joshua_start_minutes)
    meeting_window_end = joshua_end_minutes
    
    # Check if valid meeting window exists
    if meeting_window_end - meeting_window_start < min_meeting_duration:
        itinerary = []
    else:
        # Schedule meeting for minimum required duration at earliest possible time
        meeting_start = meeting_window_start
        meeting_end = meeting_start + min_meeting_duration
        
        # Calculate departure time from start location
        departure_time = meeting_start - travel_time_to_ggp
        
        # Create travel action
        travel_action = {
            "action": "travel",
            "start_location": start_location,
            "end_location": joshua_location,
            "start_time": minutes_to_time(departure_time),
            "end_time": minutes_to_time(meeting_start)
        }
        # Create meet action
        meet_action = {
            "action": "meet",
            "location": joshua_location,
            "person": joshua_person,
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        }
        itinerary = [travel_action, meet_action]
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()