import json

def calculate_optimal_schedule():
    # Input parameters
    arrival_time = "9:00"
    robert_available_start = "11:15"
    robert_available_end = "17:45"
    min_meeting_duration = 120  # minutes
    travel_nob_to_presidio = 17  # minutes
    travel_presidio_to_nob = 18  # minutes
    
    # Convert time strings to minutes since midnight
    def time_to_minutes(time_str):
        h, m = map(int, time_str.split(':'))
        return h * 60 + m
    
    arrival_min = time_to_minutes(arrival_time)
    robert_start_min = time_to_minutes(robert_available_start)
    robert_end_min = time_to_minutes(robert_available_end)
    
    # Calculate earliest possible meeting start
    # Need to travel from Nob Hill to Presidio
    earliest_arrival_presidio = arrival_min + travel_nob_to_presidio
    meeting_start = max(earliest_arrival_presidio, robert_start_min)
    
    # Calculate meeting end time (must be before Robert's availability ends)
    meeting_end = min(meeting_start + min_meeting_duration, robert_end_min)
    
    # Check if meeting duration is sufficient
    actual_duration = meeting_end - meeting_start
    if actual_duration < min_meeting_duration:
        return {"itinerary": []}  # No feasible schedule
    
    # Convert minutes back to time strings
    def minutes_to_time(m):
        h = m // 60
        m = m % 60
        return f"{h}:{m:02d}"
    
    # Create itinerary
    itinerary = [
        {
            "action": "travel",
            "location": "Presidio",
            "person": "self",
            "start_time": minutes_to_time(arrival_min),
            "end_time": minutes_to_time(earliest_arrival_presidio)
        },
        {
            "action": "meet",
            "location": "Presidio",
            "person": "Robert",
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        }
    ]
    
    return {"itinerary": itinerary}

# Compute and output the schedule
schedule = calculate_optimal_schedule()
print(json.dumps(schedule, indent=2))