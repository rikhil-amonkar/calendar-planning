from z3 import *
import json
from itertools import combinations

def solve_scheduling():
    s = Solver()

    # Friend data with locations and time windows
    friends = {
        "Elizabeth": {"location": "Financial District", "start": "10:00", "end": "12:45", "duration": 75},
        "Joseph": {"location": "Union Square", "start": "11:45", "end": "14:45", "duration": 120},
        "Ashley": {"location": "Russian Hill", "start": "11:30", "end": "21:30", "duration": 45},
        "Karen": {"location": "Mission District", "start": "14:15", "end": "22:00", "duration": 30},
        "Richard": {"location": "Fisherman's Wharf", "start": "14:30", "end": "17:30", "duration": 30},
        "Kimberly": {"location": "Haight-Ashbury", "start": "14:15", "end": "17:30", "duration": 105},
        "Helen": {"location": "Sunset District", "start": "14:45", "end": "20:45", "duration": 105},
        "Robert": {"location": "Presidio", "start": "21:45", "end": "22:45", "duration": 60}
    }

    # Travel times between locations
    travel_times = {
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "Mission District"): 20,
        ("Marina District", "Fisherman's Wharf"): 10,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Presidio"): 10,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Russian Hill"): 11,
        ("Financial District", "Mission District"): 17,
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Sunset District"): 30,
        ("Financial District", "Presidio"): 22,
        ("Union Square", "Russian Hill"): 13,
        ("Union Square", "Mission District"): 14,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Sunset District"): 27,
        ("Union Square", "Presidio"): 24,
        ("Russian Hill", "Mission District"): 16,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Presidio"): 14,
        ("Mission District", "Fisherman's Wharf"): 22,
        ("Mission District", "Haight-Ashbury"): 12,
        ("Mission District", "Sunset District"): 24,
        ("Mission District", "Presidio"): 25,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Sunset District"): 27,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Sunset District", "Presidio"): 16
    }

    # Helper functions for time conversion
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm - 540  # 9:00 AM is 540 minutes

    def minutes_to_time(minutes):
        total = minutes + 540
        hh = total // 60
        mm = total % 60
        return f"{hh:02d}:{mm:02d}"

    # Create variables for each meeting
    meetings = {}
    for name in friends:
        start = Int(f"start_{name}")
        end = Int(f"end_{name}")
        meetings[name] = {"start": start, "end": end, "loc": friends[name]["location"]}

    # Base constraints for each meeting
    for name, details in friends.items():
        start_time = time_to_minutes(details["start"])
        end_time = time_to_minutes(details["end"])
        duration = details["duration"]
        
        s.add(meetings[name]["start"] >= start_time)
        s.add(meetings[name]["end"] <= end_time)
        s.add(meetings[name]["end"] == meetings[name]["start"] + duration)

    # Create a sequence variable to determine meeting order
    sequence = {name: Int(f"seq_{name}") for name in friends}
    s.add(Distinct([sequence[name] for name in friends]))
    for name in friends:
        s.add(sequence[name] >= 1)
        s.add(sequence[name] <= len(friends))

    # Add travel time constraints between consecutive meetings
    for name1, name2 in combinations(friends.keys(), 2):
        loc1 = meetings[name1]["loc"]
        loc2 = meetings[name2]["loc"]
        travel_time = travel_times.get((loc1, loc2), travel_times.get((loc2, loc1), 0))
        
        s.add(If(sequence[name1] < sequence[name2],
                 meetings[name2]["start"] >= meetings[name1]["end"] + travel_time,
                 meetings[name1]["start"] >= meetings[name2]["end"] + travel_time))

    # Starting point - first meeting must be reachable from Marina District
    for name in friends:
        travel_time = travel_times.get(("Marina District", meetings[name]["loc"]), 0)
        s.add(Implies(sequence[name] == 1, meetings[name]["start"] >= travel_time))

    # Check if solution exists
    if s.check() == sat:
        model = s.model()
        # Get the meeting order
        ordered_meetings = sorted(friends.keys(), key=lambda x: model[sequence[x]].as_long())
        
        itinerary = []
        for name in ordered_meetings:
            start = model[meetings[name]["start"]].as_long()
            end = model[meetings[name]["end"]].as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end),
                "location": meetings[name]["loc"]
            })
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid schedule found"}

solution = solve_scheduling()
print(json.dumps(solution, indent=2))