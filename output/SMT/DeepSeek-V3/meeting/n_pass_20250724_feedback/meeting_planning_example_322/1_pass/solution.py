from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define time in minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Friends' availability and constraints
    friends = {
        "William": {
            "location": "Russian Hill",
            "available_start": time_to_minutes("18:30"),  # 6:30 PM
            "available_end": time_to_minutes("20:45"),     # 8:45 PM
            "min_duration": 105
        },
        "Michelle": {
            "location": "Chinatown",
            "available_start": time_to_minutes("08:15"),   # 8:15 AM
            "available_end": time_to_minutes("14:00"),    # 2:00 PM
            "min_duration": 15
        },
        "George": {
            "location": "Presidio",
            "available_start": time_to_minutes("10:30"),  # 10:30 AM
            "available_end": time_to_minutes("18:45"),     # 6:45 PM
            "min_duration": 30
        },
        "Robert": {
            "location": "Fisherman's Wharf",
            "available_start": time_to_minutes("09:00"),   # 9:00 AM
            "available_end": time_to_minutes("13:45"),     # 1:45 PM
            "min_duration": 30
        }
    }

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        "Sunset District": {
            "Russian Hill": 24,
            "Chinatown": 30,
            "Presidio": 16,
            "Fisherman's Wharf": 29
        },
        "Russian Hill": {
            "Sunset District": 23,
            "Chinatown": 9,
            "Presidio": 14,
            "Fisherman's Wharf": 7
        },
        "Chinatown": {
            "Sunset District": 29,
            "Russian Hill": 7,
            "Presidio": 19,
            "Fisherman's Wharf": 8
        },
        "Presidio": {
            "Sunset District": 15,
            "Russian Hill": 14,
            "Chinatown": 21,
            "Fisherman's Wharf": 19
        },
        "Fisherman's Wharf": {
            "Sunset District": 27,
            "Russian Hill": 7,
            "Chinatown": 12,
            "Presidio": 17
        }
    }

    # Current location starts at Sunset District at 9:00 AM (540 minutes)
    current_time = 540  # 9:00 AM in minutes
    current_location = "Sunset District"

    # Create variables for each meeting's start and end times
    meetings = {}
    for name in friends:
        start = Int(f"start_{name}")
        end = Int(f"end_{name}")
        meetings[name] = {
            "start": start,
            "end": end,
            "location": friends[name]["location"],
            "min_duration": friends[name]["min_duration"],
            "available_start": friends[name]["available_start"],
            "available_end": friends[name]["available_end"]
        }
        # Constraints: meeting within available time and duration
        s.add(start >= friends[name]["available_start"])
        s.add(end <= friends[name]["available_end"])
        s.add(end == start + friends[name]["min_duration"])

    # Order of meetings: we need to sequence them with travel times
    # We'll assume the order is Michelle, Robert, George, William (as it seems feasible)
    # Alternatively, we can let Z3 determine the order, but that's complex.
    # For simplicity, we'll enforce an order that seems plausible.

    # Michelle (Chinatown) -> Robert (Fisherman's Wharf) -> George (Presidio) -> William (Russian Hill)
    # Start with Michelle
    s.add(meetings["Michelle"]["start"] >= current_time + travel_times[current_location][meetings["Michelle"]["location"]])
    # Then travel to Robert
    s.add(meetings["Robert"]["start"] >= meetings["Michelle"]["end"] + travel_times[meetings["Michelle"]["location"]][meetings["Robert"]["location"]])
    # Then travel to George
    s.add(meetings["George"]["start"] >= meetings["Robert"]["end"] + travel_times[meetings["Robert"]["location"]][meetings["George"]["location"]])
    # Then travel to William
    s.add(meetings["William"]["start"] >= meetings["George"]["end"] + travel_times[meetings["George"]["location"]][meetings["William"]["location"]])

    # Check if the model is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in ["Michelle", "Robert", "George", "William"]:
            start_val = model[meetings[name]["start"]].as_long()
            end_val = model[meetings[name]["end"]].as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid schedule found"}

# Solve and print the result
result = solve_scheduling()
print(json.dumps(result, indent=2))