import json

def calculate_optimal_schedule():
    # Input parameters
    arrival_time = "9:00"
    arrival_location = "Alamo Square"
    timothy_location = "Richmond District"
    timothy_available_start = "20:45"
    timothy_available_end = "21:30"
    min_meeting_duration = 45  # minutes
    travel_to_richmond = 12  # minutes
    travel_back = 13  # minutes
    
    # Convert times to minutes since midnight for easier calculations
    def time_to_minutes(time_str):
        h, m = map(int, time_str.split(':'))
        return h * 60 + m
    
    arrival_min = time_to_minutes(arrival_time)
    timothy_start_min = time_to_minutes(timothy_available_start)
    timothy_end_min = time_to_minutes(timothy_available_end)
    
    # Calculate latest possible start time for meeting with Timothy
    meeting_duration = min_meeting_duration
    latest_start_time = timothy_end_min - meeting_duration
    
    # Calculate when we need to leave Alamo Square to arrive at latest_start_time
    leave_time = latest_start_time - travel_to_richmond
    
    # Check if we have enough time to meet Timothy
    if leave_time >= arrival_min:
        # We can meet Timothy
        meet_start = latest_start_time
        meet_end = meet_start + meeting_duration
        return {
            "itinerary": [
                {
                    "action": "travel",
                    "location": arrival_location,
                    "person": None,
                    "start_time": minutes_to_time(arrival_min),
                    "end_time": minutes_to_time(leave_time)
                },
                {
                    "action": "travel",
                    "location": timothy_location,
                    "person": None,
                    "start_time": minutes_to_time(leave_time),
                    "end_time": minutes_to_time(meet_start)
                },
                {
                    "action": "meet",
                    "location": timothy_location,
                    "person": "Timothy",
                    "start_time": minutes_to_time(meet_start),
                    "end_time": minutes_to_time(meet_end)
                }
            ]
        }
    else:
        # Cannot meet Timothy
        return {
            "itinerary": [
                {
                    "action": "stay",
                    "location": arrival_location,
                    "person": None,
                    "start_time": minutes_to_time(arrival_min),
                    "end_time": minutes_to_time(arrival_min + 60)  # arbitrary 1 hour stay
                }
            ]
        }

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Calculate and print the optimal schedule
optimal_schedule = calculate_optimal_schedule()
print(json.dumps(optimal_schedule, indent=2))