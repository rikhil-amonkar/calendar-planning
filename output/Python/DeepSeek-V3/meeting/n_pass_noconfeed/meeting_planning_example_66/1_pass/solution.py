import json

def calculate_optimal_schedule():
    # Input parameters
    arrival_time = "9:00"
    robert_available_start = "11:15"
    robert_available_end = "17:45"
    min_meeting_duration = 120  # minutes
    travel_nob_to_presidio = 17  # minutes
    travel_presidio_to_nob = 18  # minutes
    
    # Convert time strings to minutes since 9:00 (arrival time)
    def time_to_minutes(time_str):
        h, m = map(int, time_str.split(':'))
        return (h - 9) * 60 + m
    
    def minutes_to_time(minutes):
        total_h = 9 + minutes // 60
        total_m = minutes % 60
        return f"{total_h}:{total_m:02d}"
    
    robert_start = time_to_minutes(robert_available_start)
    robert_end = time_to_minutes(robert_available_end)
    
    # Calculate possible meeting windows
    # Earliest you can arrive at Presidio: 9:00 + 17 min travel = 9:17
    earliest_arrival_presidio = time_to_minutes("9:00") + travel_nob_to_presidio
    # You can stay until robert_end (17:45), but need to leave 18 min before to return to Nob Hill
    latest_departure_presidio = robert_end - travel_presidio_to_nob
    
    # Possible meeting start is max(earliest_arrival_presidio, robert_start)
    meeting_start = max(earliest_arrival_presidio, robert_start)
    # Possible meeting end is min(meeting_start + min_meeting_duration, latest_departure_presidio)
    meeting_end = min(meeting_start + min_meeting_duration, latest_departure_presidio)
    
    # Check if meeting is possible
    if meeting_end - meeting_start >= min_meeting_duration:
        meet_start_time = minutes_to_time(meeting_start)
        meet_end_time = minutes_to_time(meeting_end)
        itinerary = [
            {
                "action": "travel",
                "location": "Presidio",
                "person": "None",
                "start_time": "9:00",
                "end_time": minutes_to_time(earliest_arrival_presidio)
            },
            {
                "action": "meet",
                "location": "Presidio",
                "person": "Robert",
                "start_time": meet_start_time,
                "end_time": meet_end_time
            },
            {
                "action": "travel",
                "location": "Nob Hill",
                "person": "None",
                "start_time": meet_end_time,
                "end_time": minutes_to_time(meeting_end + travel_presidio_to_nob)
            }
        ]
    else:
        itinerary = []
    
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

calculate_optimal_schedule()