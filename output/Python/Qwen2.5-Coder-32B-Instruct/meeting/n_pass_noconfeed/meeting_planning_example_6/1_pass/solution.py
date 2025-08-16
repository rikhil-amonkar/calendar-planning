import json
from datetime import datetime, timedelta

# Input parameters
arrival_time = "9:00"
travel_time = 11  # in minutes
kenneth_start = "14:15"
kenneth_end = "19:45"
kenneth_min_meeting_time = 90  # in minutes

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m}" if h > 9 else f"{h}:{m:02}"

def calculate_schedule():
    arrival_minutes = time_to_minutes(arrival_time)
    kenneth_start_minutes = time_to_minutes(kenneth_start)
    kenneth_end_minutes = time_to_minutes(kenneth_end)
    
    # Calculate the latest possible start time for meeting Kenneth
    latest_start_for_kenneth = kenneth_end_minutes - kenneth_min_meeting_time
    
    # Determine if we can meet Kenneth
    if arrival_minutes + travel_time <= latest_start_for_kenneth:
        # We can meet Kenneth
        meeting_start = max(arrival_minutes + travel_time, kenneth_start_minutes)
        meeting_end = meeting_start + kenneth_min_meeting_time
        
        itinerary = [
            {
                "action": "meet",
                "location": "Nob Hill",
                "person": "Kenneth",
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            }
        ]
    else:
        # Cannot meet Kenneth for the required duration
        itinerary = []
    
    return itinerary

def main():
    itinerary = calculate_schedule()
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()