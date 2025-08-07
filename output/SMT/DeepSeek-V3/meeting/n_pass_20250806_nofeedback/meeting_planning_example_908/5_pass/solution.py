from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define friends and constraints
    friends = [
        {"name": "Mark", "location": "Fisherman's Wharf", "available_start": "8:15", "available_end": "10:00", "duration": 30},
        {"name": "Stephanie", "location": "Presidio", "available_start": "12:15", "available_end": "15:00", "duration": 75},
        {"name": "Betty", "location": "Bayview", "available_start": "7:15", "available_end": "20:30", "duration": 15},
        {"name": "Lisa", "location": "Haight-Ashbury", "available_start": "15:30", "available_end": "18:30", "duration": 45},
        {"name": "William", "location": "Russian Hill", "available_start": "18:45", "available_end": "20:00", "duration": 60},
        {"name": "Brian", "location": "The Castro", "available_start": "9:15", "available_end": "13:15", "duration": 30},
        {"name": "Joseph", "location": "Marina District", "available_start": "10:45", "available_end": "15:00", "duration": 90},
        {"name": "Ashley", "location": "Richmond District", "available_start": "9:45", "available_end": "11:15", "duration": 45},
        {"name": "Patricia", "location": "Union Square", "available_start": "16:30", "available_end": "20:00", "duration": 120},
        {"name": "Karen", "location": "Sunset District", "available_start": "16:30", "available_end": "22:00", "duration": 105}
    ]

    # Time conversion functions
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Travel times dictionary (simplified for example)
    travel_times = {
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Bayview"): 19,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Russian Hill"): 11,
        ("Financial District", "The Castro"): 20,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Sunset District"): 30,
        # Add reverse directions
        ("Fisherman's Wharf", "Financial District"): 10,
        ("Presidio", "Financial District"): 22,
        ("Bayview", "Financial District"): 19,
        ("Haight-Ashbury", "Financial District"): 19,
        ("Russian Hill", "Financial District"): 11,
        ("The Castro", "Financial District"): 20,
        ("Marina District", "Financial District"): 15,
        ("Richmond District", "Financial District"): 21,
        ("Union Square", "Financial District"): 9,
        ("Sunset District", "Financial District"): 30,
    }

    # Create meeting variables
    meetings = []
    for friend in friends:
        start = Int(f"start_{friend['name']}")
        end = Int(f"end_{friend['name']}")
        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        duration = friend["duration"]
        
        meetings.append({
            "name": friend["name"],
            "location": friend["location"],
            "start": start,
            "end": end,
            "available_start": available_start,
            "available_end": available_end,
            "duration": duration,
            "scheduled": Bool(f"scheduled_{friend['name']}")  # Track if meeting is scheduled
        })

    # Arrival time at Financial District
    arrival_time = 540  # 9:00 AM in minutes

    # Constraints for each meeting
    for meeting in meetings:
        # If meeting is scheduled, it must be within its window
        s.add(Implies(meeting["scheduled"], 
                     And(meeting["start"] >= meeting["available_start"],
                         meeting["end"] <= meeting["available_end"],
                         meeting["end"] == meeting["start"] + meeting["duration"])))
        
        # If not scheduled, set start/end to 0
        s.add(Implies(Not(meeting["scheduled"]), 
                     And(meeting["start"] == 0, meeting["end"] == 0)))

    # Sequence constraints - ensure travel time between consecutive meetings
    for i in range(len(meetings)):
        for j in range(len(meetings)):
            if i != j:
                travel_time = travel_times.get((meetings[i]["location"], meetings[j]["location"]), 0)
                # If both meetings are scheduled, ensure enough time between them
                s.add(Implies(And(meetings[i]["scheduled"], meetings[j]["scheduled"]),
                         Or(meetings[j]["start"] >= meetings[i]["end"] + travel_time,
                            meetings[i]["start"] >= meetings[j]["end"] + travel_time)))

    # First meeting must be after arrival time
    for meeting in meetings:
        s.add(Implies(meeting["scheduled"], meeting["start"] >= arrival_time))

    # Maximize number of scheduled meetings
    num_scheduled = Int("num_scheduled")
    s.add(num_scheduled == Sum([If(m["scheduled"], 1, 0) for m in meetings]))
    maximize(s, num_scheduled)

    # Solve
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for meeting in meetings:
            if is_true(m[meeting["scheduled"]]):
                start_val = m[meeting["start"]].as_long()
                end_val = m[meeting["end"]].as_long()
                itinerary.append({
                    "action": "meet",
                    "person": meeting["name"],
                    "start_time": minutes_to_time(start_val),
                    "end_time": minutes_to_time(end_val)
                })
        # Sort by start time
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve and print result
result = solve_scheduling()
print("SOLUTION:")
print(json.dumps(result, indent=2))