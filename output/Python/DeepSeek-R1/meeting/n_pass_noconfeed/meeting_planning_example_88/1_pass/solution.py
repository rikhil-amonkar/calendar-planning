import json

def main():
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        return int(parts[0]) * 60 + int(parts[1])
    
    def minutes_to_time(mins):
        hours = mins // 60
        minutes = mins % 60
        return f"{hours}:{minutes:02d}"

    # Input parameters
    arrival_sunset_str = "9:00"
    joshua_start_str = "20:45"
    joshua_end_str = "21:45"
    travel_sunset_to_park = 11

    # Convert times to minutes
    arrival_sunset = time_to_minutes(arrival_sunset_str)
    joshua_start = time_to_minutes(joshua_start_str)
    joshua_end = time_to_minutes(joshua_end_str)
    
    # Calculate departure time from Sunset
    leave_sunset = joshua_start - travel_sunset_to_park
    
    if leave_sunset < arrival_sunset:
        # If we can't leave early enough, leave immediately upon arrival
        actual_arrival = arrival_sunset + travel_sunset_to_park
        if actual_arrival >= joshua_end:
            meeting = None
        else:
            meeting_start = max(actual_arrival, joshua_start)
            if joshua_end - meeting_start < 15:
                meeting = None
            else:
                meeting = {
                    "action": "meet",
                    "location": "Golden Gate Park",
                    "person": "Joshua",
                    "start_time": minutes_to_time(meeting_start),
                    "end_time": minutes_to_time(joshua_end)
                }
    else:
        # Normal case: leave at calculated time
        meeting_duration = joshua_end - joshua_start
        if meeting_duration < 15:
            meeting = None
        else:
            meeting = {
                "action": "meet",
                "location": "Golden Gate Park",
                "person": "Joshua",
                "start_time": joshua_start_str,
                "end_time": joshua_end_str
            }
    
    itinerary = []
    if meeting is not None:
        itinerary.append(meeting)
    
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()