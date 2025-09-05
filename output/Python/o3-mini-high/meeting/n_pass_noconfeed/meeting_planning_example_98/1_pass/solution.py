import json

def time_to_minutes(time_str):
    # Convert a time string like '9:00' or '20:45' to minutes since midnight.
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    # Convert minutes since midnight to a time string in H:MM format.
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Input parameters
    arrival_alamo = "9:00"            # Arrival at Alamo Square
    timothy_avail_start = "20:45"     # Timothy is available at Richmond District starting at 20:45
    timothy_avail_end = "21:30"       # Timothy is available until 21:30
    min_meeting_duration = 45         # Minimum meeting duration in minutes

    # Travel times (in minutes)
    travel_alamo_to_richmond = 12
    travel_richmond_to_alamo = 13

    # Convert times to minutes since midnight
    arrival_alamo_min = time_to_minutes(arrival_alamo)
    timothy_start_min = time_to_minutes(timothy_avail_start)
    timothy_end_min = time_to_minutes(timothy_avail_end)

    # Calculate the required departure time from Alamo Square in order to reach Richmond District by timothy_start_min
    departure_from_alamo = timothy_start_min - travel_alamo_to_richmond

    # Check that departure time is not before arrival time
    if departure_from_alamo < arrival_alamo_min:
        output = {"error": "Scheduling conflict: Cannot depart Alamo Square before arrival."}
        print(json.dumps(output))
        return

    # Check if Timothy's available window meets the minimum meeting duration requirement
    available_duration = timothy_end_min - timothy_start_min
    if available_duration < min_meeting_duration:
        output = {"error": "Scheduling conflict: Timothy's availability does not meet the minimum meeting duration."}
        print(json.dumps(output))
        return

    # For the optimal schedule, you'll wait at Alamo Square until departure_from_alamo,
    # travel for travel_alamo_to_richmond minutes, and then meet Timothy at Richmond District.
    # The meeting with Timothy will occur from his availability start to end time.
    # (The waiting and travel times are accounted for in the scheduling even though they are not separate meetings.)
    meeting_with_timothy = {
        "action": "meet",
        "location": "Richmond District",
        "person": "Timothy",
        "start_time": minutes_to_time(timothy_start_min),
        "end_time": minutes_to_time(timothy_end_min)
    }

    # Although the sample itinerary structure shows two events,
    # here the optimal schedule based on the constraints has one meeting event.
    itinerary = [meeting_with_timothy]

    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()