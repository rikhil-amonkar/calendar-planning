import json
import itertools

def time_to_minutes(t):
    # Convert time string "H:MM" to minutes since midnight
    parts = t.split(":")
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(m):
    # Convert minutes since midnight to time string "H:MM" (24-hour format, no leading zero for hour)
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def schedule_meetings(order, start_time, start_location, travel_times):
    current_time = start_time
    current_location = start_location
    itinerary = []
    for meeting in order:
        # Compute travel from current location to the meeting location
        travel_time = travel_times[current_location][meeting["location"]]
        arrival_time = current_time + travel_time
        # Meeting cannot start before the friend's available start time
        meeting_start = max(arrival_time, meeting["avail_start"])
        meeting_end = meeting_start + meeting["min_duration"]
        # Check if the meeting can finish before the friend's available end time
        if meeting_end > meeting["avail_end"]:
            return None  # This schedule is not feasible
        # Append the meeting details to the itinerary
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["person"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        # Update current time and location for the next meeting
        current_time = meeting_end
        current_location = meeting["location"]
    return itinerary

def main():
    # Define travel times in minutes between locations
    travel_times = {
        "North Beach": {"Union Square": 7, "Russian Hill": 4, "North Beach": 0},
        "Union Square": {"North Beach": 10, "Russian Hill": 13, "Union Square": 0},
        "Russian Hill": {"North Beach": 5, "Union Square": 11, "Russian Hill": 0}
    }

    # Starting constraints: arrive at North Beach at 9:00 AM
    start_location = "North Beach"
    start_time = time_to_minutes("9:00")
    
    # Define meeting constraints for each friend
    meetings = [
        {
            "person": "Emily",
            "location": "Union Square",
            "avail_start": time_to_minutes("16:00"),
            "avail_end": time_to_minutes("17:15"),
            "min_duration": 45
        },
        {
            "person": "Margaret",
            "location": "Russian Hill",
            "avail_start": time_to_minutes("19:00"),
            "avail_end": time_to_minutes("21:00"),
            "min_duration": 120
        }
    ]
    
    best_itinerary = None
    max_meetings = 0
    best_finish_time = float('inf')

    # Try all possible orders of meetings and pick the one that maximizes the number of meetings
    for order in itertools.permutations(meetings):
        itinerary = schedule_meetings(order, start_time, start_location, travel_times)
        if itinerary is not None:
            meeting_count = len(itinerary)
            # Compute finish time by simulating the schedule
            current_time = start_time
            current_location = start_location
            for meeting in order:
                travel_time = travel_times[current_location][meeting["location"]]
                arrival_time = current_time + travel_time
                meeting_start = max(arrival_time, meeting["avail_start"])
                meeting_end = meeting_start + meeting["min_duration"]
                current_time = meeting_end
                current_location = meeting["location"]
            finish_time = current_time
            if meeting_count > max_meetings or (meeting_count == max_meetings and finish_time < best_finish_time):
                best_itinerary = itinerary
                max_meetings = meeting_count
                best_finish_time = finish_time

    result = {"itinerary": best_itinerary if best_itinerary is not None else []}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()