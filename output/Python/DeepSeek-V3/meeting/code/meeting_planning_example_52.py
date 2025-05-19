import json

def calculate_optimal_schedule():
    # Input parameters
    arrival_time = "9:00"
    arrival_location = "Russian Hill"
    barbara_available_start = "13:15"
    barbara_available_end = "18:15"
    min_meeting_duration = 45  # minutes
    travel_russian_to_richmond = 14  # minutes
    travel_richmond_to_russian = 13  # minutes
    
    # Convert time strings to minutes since midnight
    def time_to_minutes(time_str):
        h, m = map(int, time_str.split(':'))
        return h * 60 + m
    
    # Convert minutes back to time string
    def minutes_to_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h}:{m:02d}"
    
    arrival_min = time_to_minutes(arrival_time)
    barbara_start_min = time_to_minutes(barbara_available_start)
    barbara_end_min = time_to_minutes(barbara_available_end)
    
    # Calculate earliest possible departure to meet Barbara
    # Need to arrive at Richmond by barbara_start_min + min_meeting_duration at latest
    latest_departure_for_meeting = barbara_end_min - min_meeting_duration - travel_russian_to_richmond
    
    # Check if we have time to meet Barbara
    if arrival_min + travel_russian_to_richmond > barbara_end_min - min_meeting_duration:
        # Not enough time to meet Barbara
        itinerary = []
    else:
        # Calculate optimal meeting time (as early as possible)
        meeting_start = max(barbara_start_min, arrival_min + travel_russian_to_richmond)
        meeting_end = meeting_start + min_meeting_duration
        
        # Create itinerary
        itinerary = [
            {
                "action": "travel",
                "location": "Richmond District",
                "person": "",
                "start_time": minutes_to_time(arrival_min),
                "end_time": minutes_to_time(arrival_min + travel_russian_to_richmond)
            },
            {
                "action": "meet",
                "location": "Richmond District",
                "person": "Barbara",
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            }
        ]
    
    # Prepare output
    output = {
        "itinerary": itinerary
    }
    
    return json.dumps(output, indent=2)

# Execute and print the result
print(calculate_optimal_schedule())