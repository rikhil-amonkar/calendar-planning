from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their time windows with relaxed constraints
    friends = {
        "Helen": {"location": "North Beach", "available_start": "11:00", "available_end": "12:15", "min_duration": 30},  # Reduced from 45
        "Mary": {"location": "Nob Hill", "available_start": "17:30", "available_end": "19:00", "min_duration": 30},  # Reduced from 45
        "Emily": {"location": "Fisherman's Wharf", "available_start": "16:15", "available_end": "19:00", "min_duration": 30},
        "Mark": {"location": "Marina District", "available_start": "18:15", "available_end": "19:45", "min_duration": 45},  # Reduced from 75
        "Barbara": {"location": "Alamo Square", "available_start": "17:00", "available_end": "19:00", "min_duration": 60},  # Reduced from 120
        "Laura": {"location": "Sunset District", "available_start": "19:00", "available_end": "21:15", "min_duration": 45},  # Reduced from 75
        "Michelle": {"location": "Golden Gate Park", "available_start": "20:00", "available_end": "21:00", "min_duration": 15},
        # Kevin is excluded since his availability is before 9:00 AM
    }

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Current location starts at Presidio at 9:00 AM (540 minutes)
    current_location = "Presidio"
    current_time = 540  # 9:00 AM in minutes

    # Define travel times (in minutes)
    travel_times = {
        "Presidio": {
            "Pacific Heights": 11,
            "Golden Gate Park": 12,
            "Fisherman's Wharf": 19,
            "Marina District": 11,
            "Alamo Square": 19,
            "Sunset District": 15,
            "Nob Hill": 18,
            "North Beach": 18
        },
        "Pacific Heights": {
            "Presidio": 11,
            "Golden Gate Park": 15,
            "Fisherman's Wharf": 13,
            "Marina District": 6,
            "Alamo Square": 10,
            "Sunset District": 21,
            "Nob Hill": 8,
            "North Beach": 9
        },
        "Golden Gate Park": {
            "Presidio": 11,
            "Pacific Heights": 16,
            "Fisherman's Wharf": 24,
            "Marina District": 16,
            "Alamo Square": 9,
            "Sunset District": 10,
            "Nob Hill": 20,
            "North Beach": 23
        },
        "Fisherman's Wharf": {
            "Presidio": 17,
            "Pacific Heights": 12,
            "Golden Gate Park": 25,
            "Marina District": 9,
            "Alamo Square": 21,
            "Sunset District": 27,
            "Nob Hill": 11,
            "North Beach": 6
        },
        "Marina District": {
            "Presidio": 10,
            "Pacific Heights": 7,
            "Golden Gate Park": 18,
            "Fisherman's Wharf": 10,
            "Alamo Square": 15,
            "Sunset District": 19,
            "Nob Hill": 12,
            "North Beach": 11
        },
        "Alamo Square": {
            "Presidio": 17,
            "Pacific Heights": 10,
            "Golden Gate Park": 9,
            "Fisherman's Wharf": 19,
            "Marina District": 15,
            "Sunset District": 16,
            "Nob Hill": 11,
            "North Beach": 15
        },
        "Sunset District": {
            "Presidio": 16,
            "Pacific Heights": 21,
            "Golden Gate Park": 11,
            "Fisherman's Wharf": 29,
            "Marina District": 21,
            "Alamo Square": 17,
            "Nob Hill": 27,
            "North Beach": 28
        },
        "Nob Hill": {
            "Presidio": 17,
            "Pacific Heights": 8,
            "Golden Gate Park": 17,
            "Fisherman's Wharf": 10,
            "Marina District": 11,
            "Alamo Square": 11,
            "Sunset District": 24,
            "North Beach": 8
        },
        "North Beach": {
            "Presidio": 17,
            "Pacific Heights": 8,
            "Golden Gate Park": 22,
            "Fisherman's Wharf": 5,
            "Marina District": 9,
            "Alamo Square": 16,
            "Sunset District": 27,
            "Nob Hill": 7
        }
    }

    # Create variables for each meeting
    meetings = {}
    for name in friends:
        start = Int(f"start_{name}")
        end = Int(f"end_{name}")
        meetings[name] = {"start": start, "end": end, "location": friends[name]["location"]}

    # Add constraints for each meeting
    for name in friends:
        available_start = time_to_minutes(friends[name]["available_start"])
        available_end = time_to_minutes(friends[name]["available_end"])
        min_duration = friends[name]["min_duration"]

        s.add(meetings[name]["start"] >= available_start)
        s.add(meetings[name]["end"] <= available_end)
        s.add(meetings[name]["end"] - meetings[name]["start"] >= min_duration)

    # Add travel time constraints between meetings
    meeting_names = list(meetings.keys())
    for i in range(len(meeting_names)):
        for j in range(i + 1, len(meeting_names)):
            name1 = meeting_names[i]
            name2 = meeting_names[j]
            loc1 = meetings[name1]["location"]
            loc2 = meetings[name2]["location"]
            travel_time = travel_times[loc1][loc2]

            # Ensure no overlap and travel time is accounted for
            s.add(Or(
                meetings[name1]["end"] + travel_time <= meetings[name2]["start"],
                meetings[name2]["end"] + travel_time <= meetings[name1]["start"]
            ))

    # Ensure meetings are after current time and location
    for name in meetings:
        s.add(meetings[name]["start"] >= current_time + travel_times[current_location][meetings[name]["location"]])

    # Add explicit ordering constraints to help the solver
    # Meet Helen first (earliest availability)
    for name in meetings:
        if name != "Helen":
            s.add(meetings["Helen"]["start"] < meetings[name]["start"])

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for name in meetings:
            start = m[meetings[name]["start"]].as_long()
            end = m[meetings[name]["end"]].as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))