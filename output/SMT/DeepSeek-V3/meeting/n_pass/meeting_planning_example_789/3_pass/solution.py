from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their details
    friends = [
        {"name": "Betty", "location": "Russian Hill", "available_start": "07:00", "available_end": "16:45", "min_duration": 105},
        {"name": "Melissa", "location": "Alamo Square", "available_start": "09:30", "available_end": "17:15", "min_duration": 105},
        {"name": "Joshua", "location": "Haight-Ashbury", "available_start": "12:15", "available_end": "19:00", "min_duration": 90},
        {"name": "Jeffrey", "location": "Marina District", "available_start": "12:15", "available_end": "18:00", "min_duration": 45},
        {"name": "James", "location": "Bayview", "available_start": "07:30", "available_end": "20:00", "min_duration": 90},
        {"name": "Anthony", "location": "Chinatown", "available_start": "11:45", "available_end": "13:30", "min_duration": 75},
        {"name": "Timothy", "location": "Presidio", "available_start": "12:30", "available_end": "14:45", "min_duration": 90},
        {"name": "Emily", "location": "Sunset District", "available_start": "19:30", "available_end": "21:30", "min_duration": 120}
    ]

    # Convert time strings to minutes since midnight
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Define travel times (in minutes)
    travel_times = {
        ("Union Square", "Russian Hill"): 13,
        ("Union Square", "Alamo Square"): 15,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Bayview"): 15,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Sunset District"): 27,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Bayview"): 23,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Sunset District"): 23,
        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Bayview"): 16,
        ("Alamo Square", "Chinatown"): 15,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Sunset District"): 16,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Sunset District"): 19,
        ("Bayview", "Chinatown"): 19,
        ("Bayview", "Presidio"): 32,
        ("Bayview", "Sunset District"): 23,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Sunset District"): 29,
        ("Presidio", "Sunset District"): 16
    }

    # Add symmetric travel times
    for (loc1, loc2), time in list(travel_times.items()):
        if (loc2, loc1) not in travel_times:
            travel_times[(loc2, loc1)] = time

    # Define variables for each meeting's start and end times
    meetings = {}
    for friend in friends:
        name = friend["name"]
        meetings[name] = {
            "start": Int(f"start_{name}"),
            "end": Int(f"end_{name}"),
            "location": friend["location"],
            "available_start": time_to_minutes(friend["available_start"]),
            "available_end": time_to_minutes(friend["available_end"]),
            "min_duration": friend["min_duration"]
        }

    # Add basic constraints for each meeting
    for name, meeting in meetings.items():
        s.add(meeting["start"] >= meeting["available_start"])
        s.add(meeting["end"] <= meeting["available_end"])
        s.add(meeting["end"] - meeting["start"] >= meeting["min_duration"])

    # Starting at Union Square at 9:00 AM (540 minutes)
    current_time = 540
    current_location = "Union Square"

    # Create a list to track meeting order
    meeting_order = []
    for name in meetings:
        meeting_order.append((meetings[name]["start"], name))

    # Add constraints for travel times between consecutive meetings
    for i in range(len(meeting_order)-1):
        start_i, name_i = meeting_order[i]
        start_j, name_j = meeting_order[i+1]
        
        loc_i = meetings[name_i]["location"]
        loc_j = meetings[name_j]["location"]
        travel_time = travel_times.get((loc_i, loc_j), 0)
        
        s.add(start_j >= meetings[name_i]["end"] + travel_time)

    # Special constraints for time-sensitive meetings
    # Anthony's meeting must be between 11:45-13:30
    s.add(meetings["Anthony"]["start"] >= time_to_minutes("11:45"))
    s.add(meetings["Anthony"]["end"] <= time_to_minutes("13:30"))
    
    # Timothy's meeting must be between 12:30-14:45
    s.add(meetings["Timothy"]["start"] >= time_to_minutes("12:30"))
    s.add(meetings["Timothy"]["end"] <= time_to_minutes("14:45"))

    # Emily's meeting must be in the evening
    s.add(meetings["Emily"]["start"] >= time_to_minutes("19:30"))
    s.add(meetings["Emily"]["end"] <= time_to_minutes("21:30"))

    # Try to schedule all meetings
    if s.check() == sat:
        model = s.model()
        itinerary = []
        
        # Get all scheduled meetings with their times
        scheduled = []
        for name, meeting in meetings.items():
            start = model[meeting["start"]].as_long()
            end = model[meeting["end"]].as_long()
            scheduled.append((start, end, name))
        
        # Sort by start time
        scheduled.sort()
        
        # Create itinerary
        for start, end, name in scheduled:
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        
        return {"itinerary": itinerary}
    else:
        # If no solution found, try relaxing constraints
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling()
print("SOLUTION:")
print(json.dumps(solution, indent=2))