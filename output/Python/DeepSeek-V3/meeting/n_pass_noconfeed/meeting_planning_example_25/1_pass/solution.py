import json

def calculate_optimal_schedule():
    # Input parameters
    arrival_time = "9:00"
    david_available_start = "16:00"
    david_available_end = "21:45"
    meet_duration = 105  # minutes
    travel_time_gp_to_china = 23  # minutes
    travel_time_china_to_gp = 23  # minutes

    # Convert time strings to minutes since midnight
    def time_to_minutes(time_str):
        h, m = map(int, time_str.split(':'))
        return h * 60 + m

    arrival_min = time_to_minutes(arrival_time)
    david_start_min = time_to_minutes(david_available_start)
    david_end_min = time_to_minutes(david_available_end)

    # Calculate possible meeting window with David
    latest_start_with_david = david_end_min - meet_duration
    if latest_start_with_david < david_start_min:
        # Not enough time to meet David
        itinerary = []
    else:
        # Calculate travel to Chinatown
        travel_start_min = latest_start_with_david - travel_time_gp_to_china
        if travel_start_min < arrival_min:
            # Not enough time to travel to meet David
            itinerary = []
        else:
            # Calculate return time
            meet_end_min = latest_start_with_david + meet_duration
            return_arrival_min = meet_end_min + travel_time_china_to_gp

            # Convert back to time strings
            def minutes_to_time(m):
                return f"{m // 60}:{m % 60:02d}"

            itinerary = [
                {
                    "action": "travel",
                    "location": "Golden Gate Park to Chinatown",
                    "person": None,
                    "start_time": minutes_to_time(travel_start_min),
                    "end_time": minutes_to_time(travel_start_min + travel_time_gp_to_china)
                },
                {
                    "action": "meet",
                    "location": "Chinatown",
                    "person": "David",
                    "start_time": minutes_to_time(latest_start_with_david),
                    "end_time": minutes_to_time(meet_end_min)
                },
                {
                    "action": "travel",
                    "location": "Chinatown to Golden Gate Park",
                    "person": None,
                    "start_time": minutes_to_time(meet_end_min),
                    "end_time": minutes_to_time(return_arrival_min)
                }
            ]

    # Output as JSON
    output = {
        "itinerary": itinerary
    }
    print(json.dumps(output, indent=2))

calculate_optimal_schedule()