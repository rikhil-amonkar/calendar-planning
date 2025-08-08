#!/usr/bin/env python3
import itertools
import json

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Define travel times (in minutes) between locations
    travel_times = {
        "Sunset District": {"North Beach": 29, "Union Square": 30, "Alamo Square": 17},
        "North Beach": {"Sunset District": 27, "Union Square": 7, "Alamo Square": 16},
        "Union Square": {"Sunset District": 26, "North Beach": 10, "Alamo Square": 15},
        "Alamo Square": {"Sunset District": 16, "North Beach": 15, "Union Square": 14}
    }
    
    # Define friends with their location, availability (in minutes from midnight) and minimum meeting duration
    # Times in minutes: 9:00 AM = 540, 15:00 = 900, 16:00 = 960, 17:30 = 1050, 18:15 = 1095, 22:00 = 1320
    friends = [
        {"name": "Sarah", "location": "North Beach", "avail_start": 16 * 60, "avail_end": 18 * 60 + 15, "duration": 60},
        {"name": "Jeffrey", "location": "Union Square", "avail_start": 15 * 60, "avail_end": 22 * 60, "duration": 75},
        {"name": "Brian", "location": "Alamo Square", "avail_start": 16 * 60, "avail_end": 17 * 60 + 30, "duration": 75}
    ]
    
    # Starting parameters: arrive at Sunset District at 9:00AM (540 minutes)
    start_location = "Sunset District"
    start_time = 9 * 60  # 540 minutes

    best_schedule = None
    best_count = 0
    best_total_duration = 0
    best_finish_time = None

    # Consider all non-empty subsets (orders) of friends
    n = len(friends)
    for r in range(1, n+1):
        for subset in itertools.combinations(friends, r):
            # Try all permutations of this subset (order matters)
            for order in itertools.permutations(subset):
                current_time = start_time
                current_location = start_location
                itinerary = []
                feasible = True
                total_meeting_duration = 0
                # Simulate the itinerary for this order
                for friend in order:
                    # Get travel time from current location to friend's location
                    travel = travel_times[current_location][friend["location"]]
                    arrival_time = current_time + travel
                    # Wait until friend is available, if arrived early
                    meeting_start = max(arrival_time, friend["avail_start"])
                    meeting_end = meeting_start + friend["duration"]
                    # Check if meeting fits within friend's availability window
                    if meeting_end > friend["avail_end"]:
                        feasible = False
                        break
                    # Append meeting event to itinerary
                    event = {
                        "action": "meet",
                        "location": friend["location"],
                        "person": friend["name"],
                        "start_time": minutes_to_time_str(meeting_start),
                        "end_time": minutes_to_time_str(meeting_end)
                    }
                    itinerary.append(event)
                    total_meeting_duration += friend["duration"]
                    # Update current time and location for the next meeting
                    current_time = meeting_end
                    current_location = friend["location"]
                if not feasible:
                    continue
                count = len(itinerary)
                finish_time = current_time
                # Choose optimal itinerary:
                # Primary: maximum count. Secondary: maximum total meeting duration.
                # Tertiary: if tied, earlier finish time.
                if (count > best_count or
                    (count == best_count and total_meeting_duration > best_total_duration) or
                    (count == best_count and total_meeting_duration == best_total_duration and (best_finish_time is None or finish_time < best_finish_time))):
                    best_count = count
                    best_total_duration = total_meeting_duration
                    best_finish_time = finish_time
                    best_schedule = itinerary

    # Build result dictionary in the required JSON structure
    result = {"itinerary": best_schedule if best_schedule is not None else []}

    # Output the result as JSON-formatted dictionary
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()