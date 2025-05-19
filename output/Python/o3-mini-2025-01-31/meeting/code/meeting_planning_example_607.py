#!/usr/bin/env python3
import json

def minutes_to_timestr(minutes):
    # Convert minutes since midnight to H:MM in 24-hour format (no leading zero for hours)
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times in minutes between districts (symmetric values are not assumed, so use provided one-way values)
    travel_times = {
        "Sunset District": {
            "Russian Hill": 24,
            "The Castro": 17,
            "Richmond District": 12,
            "Marina District": 21,
            "North Beach": 29,
            "Union Square": 30,
            "Golden Gate Park": 11
        },
        "Russian Hill": {
            "Sunset District": 23,
            "The Castro": 21,
            "Richmond District": 14,
            "Marina District": 7,
            "North Beach": 5,
            "Union Square": 11,
            "Golden Gate Park": 21
        },
        "The Castro": {
            "Sunset District": 17,
            "Russian Hill": 18,
            "Richmond District": 16,
            "Marina District": 21,
            "North Beach": 20,
            "Union Square": 19,
            "Golden Gate Park": 11
        },
        "Richmond District": {
            "Sunset District": 11,
            "Russian Hill": 13,
            "The Castro": 16,
            "Marina District": 9,
            "North Beach": 17,
            "Union Square": 21,
            "Golden Gate Park": 9
        },
        "Marina District": {
            "Sunset District": 19,
            "Russian Hill": 8,
            "The Castro": 22,
            "Richmond District": 11,
            "North Beach": 11,
            "Union Square": 16,
            "Golden Gate Park": 18
        },
        "North Beach": {
            "Sunset District": 27,
            "Russian Hill": 4,
            "The Castro": 22,
            "Richmond District": 18,
            "Marina District": 9,
            "Union Square": 7,
            "Golden Gate Park": 22
        },
        "Union Square": {
            "Sunset District": 26,
            "Russian Hill": 13,
            "The Castro": 19,
            "Richmond District": 20,
            "Marina District": 18,
            "North Beach": 10,
            "Golden Gate Park": 22
        },
        "Golden Gate Park": {
            "Sunset District": 10,
            "Russian Hill": 19,
            "The Castro": 13,
            "Richmond District": 7,
            "Marina District": 16,
            "North Beach": 24,
            "Union Square": 22
        }
    }
    
    # Meeting constraints, using minutes since midnight for start and end times
    # Helper: convert HH:MM strings to minutes
    def time_to_minutes(timestr):
        hours, minutes = map(int, timestr.split(':'))
        return hours * 60 + minutes

    # Starting point:
    start_location = "Sunset District"
    start_time = time_to_minutes("9:00")
    
    # Define contacts with their meeting location, availability window (start, end) and minimum meeting duration.
    meetings = {
        "Karen": {
            "location": "Russian Hill",
            "avail_start": time_to_minutes("20:45"),
            "avail_end": time_to_minutes("21:45"),
            "min_duration": 60
        },
        "Jessica": {
            "location": "The Castro",
            "avail_start": time_to_minutes("15:45"),
            "avail_end": time_to_minutes("19:30"),
            "min_duration": 60
        },
        "Matthew": {
            "location": "Richmond District",
            "avail_start": time_to_minutes("7:30"),
            "avail_end": time_to_minutes("15:15"),
            "min_duration": 15
        },
        "Michelle": {
            "location": "Marina District",
            "avail_start": time_to_minutes("10:30"),
            "avail_end": time_to_minutes("18:45"),
            "min_duration": 75
        },
        "Carol": {
            "location": "North Beach",
            "avail_start": time_to_minutes("12:00"),
            "avail_end": time_to_minutes("17:00"),
            "min_duration": 90
        },
        "Stephanie": {
            "location": "Union Square",
            "avail_start": time_to_minutes("10:45"),
            "avail_end": time_to_minutes("14:15"),
            "min_duration": 30
        },
        "Linda": {
            "location": "Golden Gate Park",
            "avail_start": time_to_minutes("10:45"),
            "avail_end": time_to_minutes("22:00"),
            "min_duration": 90
        }
    }
    
    # We will adopt the following meeting order (found by logically chaining available time windows and travel times):
    # 1. Matthew at Richmond District
    # 2. Stephanie at Union Square
    # 3. Michelle at Marina District
    # 4. Carol at North Beach
    # 5. Linda at Golden Gate Park
    # 6. Jessica at The Castro
    # 7. Karen at Russian Hill
    order = ["Matthew", "Stephanie", "Michelle", "Carol", "Linda", "Jessica", "Karen"]
    
    itinerary = []
    current_location = start_location
    current_time = start_time
    
    for person in order:
        meeting = meetings[person]
        dest = meeting["location"]
        # Get travel time from current location to destination
        travel_time = travel_times[current_location][dest]
        # Update current time with travel
        current_time += travel_time
        # If arrival is before contact's availability, wait till the availability start
        if current_time < meeting["avail_start"]:
            current_time = meeting["avail_start"]
        # Determine meeting start time and meeting end time
        meet_start = current_time
        meet_end = meet_start + meeting["min_duration"]
        # Ensure that the meeting fits within the contact's availability window (we assume it does based on chosen order)
        if meet_end > meeting["avail_end"]:
            # If meeting cannot fit, we could handle it but here we assume optimal selection covers all constraints.
            raise ValueError(f"Cannot schedule meeting with {person} within available slot.")
        # Append meeting to itinerary
        itinerary.append({
            "action": "meet",
            "location": dest,
            "person": person,
            "start_time": minutes_to_timestr(meet_start),
            "end_time": minutes_to_timestr(meet_end)
        })
        # Update current time and location to meeting's end and destination respectively.
        current_time = meet_end
        current_location = dest

    # Prepare output dictionary in requested JSON format
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()