import json

def calculate_optimal_schedule():
    # Input parameters
    arrival_location = "Russian Hill"
    arrival_time = "9:00"
    friends = {
        "Barbara": {
            "location": "Pacific Heights",
            "available_start": "7:15",
            "available_end": "22:00",
            "min_duration": 60  # minutes
        }
    }
    travel_times = {
        ("Russian Hill", "Pacific Heights"): 7,
        ("Pacific Heights", "Russian Hill"): 7
    }

    # Helper function to convert time string to minutes since midnight
    def time_to_minutes(time_str):
        hours, minutes = map(int, time_str.split(':'))
        return hours * 60 + minutes

    # Helper function to convert minutes back to time string
    def minutes_to_time(minutes):
        hours = minutes // 60
        minutes = minutes % 60
        return f"{hours}:{minutes:02d}"

    arrival_min = time_to_minutes(arrival_time)
    barbara_start = time_to_minutes(friends["Barbara"]["available_start"])
    barbara_end = time_to_minutes(friends["Barbara"]["available_end"])
    min_duration = friends["Barbara"]["min_duration"]
    travel_to = travel_times[(arrival_location, friends["Barbara"]["location"])]
    travel_back = travel_times[(friends["Barbara"]["location"], arrival_location)]

    # Calculate possible meeting window
    earliest_start = max(arrival_min + travel_to, barbara_start)
    latest_end = barbara_end
    latest_start = latest_end - min_duration

    if earliest_start > latest_start:
        # No feasible meeting time
        itinerary = []
    else:
        # Optimal is to meet as soon as possible
        start_time = earliest_start
        end_time = start_time + min_duration
        itinerary = [
            {
                "action": "travel",
                "location": friends["Barbara"]["location"],
                "person": None,
                "start_time": minutes_to_time(arrival_min),
                "end_time": minutes_to_time(arrival_min + travel_to)
            },
            {
                "action": "meet",
                "location": friends["Barbara"]["location"],
                "person": "Barbara",
                "start_time": minutes_to_time(start_time),
                "end_time": minutes_to_time(end_time)
            },
            {
                "action": "travel",
                "location": arrival_location,
                "person": None,
                "start_time": minutes_to_time(end_time),
                "end_time": minutes_to_time(end_time + travel_back)
            }
        ]

    result = {
        "itinerary": itinerary
    }
    return json.dumps(result, indent=2)

print(calculate_optimal_schedule())