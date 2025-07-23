import json

def calculate_optimal_schedule():
    # Input parameters
    arrival_location = "Russian Hill"
    arrival_time = "9:00"
    
    # Barbara's availability
    barbara_location = "Richmond District"
    barbara_start = "13:15"
    barbara_end = "18:15"
    min_meeting_duration = 45  # minutes
    
    # Travel times (in minutes)
    travel_times = {
        ("Russian Hill", "Richmond District"): 14,
        ("Richmond District", "Russian Hill"): 13
    }
    
    # Convert time strings to minutes since midnight
    def time_to_minutes(time_str):
        h, m = map(int, time_str.split(':'))
        return h * 60 + m
    
    # Convert minutes back to time string
    def minutes_to_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h}:{m:02d}"
    
    barbara_start_min = time_to_minutes(barbara_start)
    barbara_end_min = time_to_minutes(barbara_end)
    arrival_min = time_to_minutes(arrival_time)
    
    # Calculate possible meeting window
    # Earliest we can arrive at Barbara's location
    earliest_arrival = arrival_min + travel_times[(arrival_location, barbara_location)]
    
    # Latest we can leave Barbara's location to get back to Russian Hill before her window closes
    # (though in this case we don't have a return constraint)
    
    # Meeting must start between max(earliest_arrival, barbara_start) and barbara_end - min_meeting_duration
    meeting_start = max(earliest_arrival, barbara_start_min)
    meeting_end = meeting_start + min_meeting_duration
    
    if meeting_end > barbara_end_min:
        # No possible meeting
        itinerary = []
    else:
        itinerary = [
            {
                "action": "travel",
                "location": barbara_location,
                "person": None,
                "start_time": minutes_to_time(arrival_min),
                "end_time": minutes_to_time(earliest_arrival)
            },
            {
                "action": "meet",
                "location": barbara_location,
                "person": "Barbara",
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            }
        ]
    
    result = {
        "itinerary": itinerary
    }
    
    return json.dumps(result, indent=2)

if __name__ == "__main__":
    print(calculate_optimal_schedule())