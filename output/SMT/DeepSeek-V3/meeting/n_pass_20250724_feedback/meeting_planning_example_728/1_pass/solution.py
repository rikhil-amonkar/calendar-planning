from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define the friends and their details
    friends = {
        "Karen": {"location": "Mission District", "start": "14:15", "end": "22:00", "duration": 30},
        "Richard": {"location": "Fisherman's Wharf", "start": "14:30", "end": "17:30", "duration": 30},
        "Robert": {"location": "Presidio", "start": "21:45", "end": "22:45", "duration": 60},
        "Joseph": {"location": "Union Square", "start": "11:45", "end": "14:45", "duration": 120},
        "Helen": {"location": "Sunset District", "start": "14:45", "end": "20:45", "duration": 105},
        "Elizabeth": {"location": "Financial District", "start": "10:00", "end": "12:45", "duration": 75},
        "Kimberly": {"location": "Haight-Ashbury", "start": "14:15", "end": "17:30", "duration": 105},
        "Ashley": {"location": "Russian Hill", "start": "11:30", "end": "21:30", "duration": 45}
    }

    # Travel times dictionary (simplified for this problem)
    travel_times = {
        ("Marina District", "Mission District"): 20,
        ("Marina District", "Fisherman's Wharf"): 10,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Russian Hill"): 8,
        ("Mission District", "Marina District"): 19,
        ("Mission District", "Fisherman's Wharf"): 22,
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Union Square"): 15,
        ("Mission District", "Sunset District"): 24,
        ("Mission District", "Financial District"): 15,
        ("Mission District", "Haight-Ashbury"): 12,
        ("Mission District", "Russian Hill"): 15,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "Mission District"): 22,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Union Square"): 13,
        ("Fisherman's Wharf", "Sunset District"): 27,
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Mission District"): 26,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Russian Hill"): 14,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Mission District"): 14,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Sunset District"): 27,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Russian Hill"): 13,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Mission District"): 25,
        ("Sunset District", "Fisherman's Wharf"): 29,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Russian Hill"): 24,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Mission District"): 17,
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Sunset District"): 30,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Russian Hill"): 11,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Mission District"): 11,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Mission District"): 16,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Union Square"): 10,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Haight-Ashbury"): 17
    }

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm - 540  # 9:00 AM is 540 minutes

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        total = minutes + 540
        hh = total // 60
        mm = total % 60
        return f"{hh:02d}:{mm:02d}"

    # Create variables for each meeting's start and end times
    meetings = {}
    for name in friends:
        start = Int(f"start_{name}")
        end = Int(f"end_{name}")
        meetings[name] = {"start": start, "end": end}

    # Current location starts at Marina District
    current_location = "Marina District"
    last_end_time = 0  # 9:00 AM is time 0 in our model

    # Constraints for each friend
    for name, details in friends.items():
        start_time = time_to_minutes(details["start"])
        end_time = time_to_minutes(details["end"])
        duration = details["duration"]

        # Meeting must start and end within the friend's availability
        s.add(meetings[name]["start"] >= start_time)
        s.add(meetings[name]["end"] <= end_time)
        s.add(meetings[name]["end"] == meetings[name]["start"] + duration)

        # Travel time from current location to friend's location
        travel_time = travel_times.get((current_location, details["location"]), 0)
        s.add(meetings[name]["start"] >= last_end_time + travel_time)

        # Update current location and last end time
        current_location = details["location"]
        last_end_time = meetings[name]["end"]

    # Ensure meetings don't overlap (simplified for this problem)
    # This is a basic constraint; a more complex model would handle ordering
    for name1, meeting1 in meetings.items():
        for name2, meeting2 in meetings.items():
            if name1 != name2:
                s.add(Or(
                    meeting1["end"] <= meeting2["start"],
                    meeting2["end"] <= meeting1["start"]
                ))

    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in friends:
            start = model[meetings[name]["start"]].as_long()
            end = model[meetings[name]["end"]].as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid schedule found"}

# Solve and print the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))