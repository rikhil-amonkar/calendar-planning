import json

def calculate_optimal_schedule():
    # Input parameters
    arrival_location = "Russian Hill"
    arrival_time = "9:00"
    daniel_location = "Richmond District"
    daniel_available_start = "19:00"
    daniel_available_end = "20:15"
    min_meeting_duration = 75  # minutes
    travel_time_to_richmond = 14  # minutes
    travel_time_back = 13  # minutes

    # Convert times to minutes since midnight for easier calculations
    def time_to_minutes(time_str):
        hours, minutes = map(int, time_str.split(':'))
        return hours * 60 + minutes

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"

    arrival_min = time_to_minutes(arrival_time)
    daniel_start_min = time_to_minutes(daniel_available_start)
    daniel_end_min = time_to_minutes(daniel_available_end)

    # Calculate the latest possible start time for the meeting to last 75 minutes
    latest_start_time = daniel_end_min - min_meeting_duration
    if latest_start_time < daniel_start_min:
        latest_start_time = daniel_start_min

    # Calculate the time to leave Russian Hill to arrive at the latest start time
    leave_time = latest_start_time - travel_time_to_richmond

    # Check if there's enough time to meet Daniel
    if leave_time < arrival_min:
        # Not possible to meet Daniel, return empty itinerary
        itinerary = []
    else:
        # Create the itinerary
        itinerary = [
            {
                "action": "travel",
                "location": "Richmond District",
                "person": None,
                "start_time": minutes_to_time(leave_time),
                "end_time": minutes_to_time(leave_time + travel_time_to_richmond)
            },
            {
                "action": "meet",
                "location": "Richmond District",
                "person": "Daniel",
                "start_time": minutes_to_time(latest_start_time),
                "end_time": minutes_to_time(latest_start_time + min_meeting_duration)
            },
            {
                "action": "travel",
                "location": "Russian Hill",
                "person": None,
                "start_time": minutes_to_time(latest_start_time + min_meeting_duration),
                "end_time": minutes_to_time(latest_start_time + min_meeting_duration + travel_time_back)
            }
        ]

    # Prepare the output
    output = {
        "itinerary": itinerary
    }

    return json.dumps(output, indent=2)

# Execute the function and print the result
print(calculate_optimal_schedule())