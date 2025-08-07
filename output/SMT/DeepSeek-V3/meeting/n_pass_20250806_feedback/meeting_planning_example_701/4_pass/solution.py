from z3 import *
import json

# Define travel times between locations
travel_times = {
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Richmond District"): 20,
    # ... (include all other travel times from previous solutions)
}

friends = {
    "Lisa": {"location": "The Castro", "start": (19, 15), "end": (21, 15), "min_duration": 120, "priority": 3},
    "Daniel": {"location": "Nob Hill", "start": (8, 15), "end": (11, 0), "min_duration": 15, "priority": 1},
    "Elizabeth": {"location": "Presidio", "start": (21, 15), "end": (22, 15), "min_duration": 45, "priority": 2},
    "Steven": {"location": "Marina District", "start": (16, 30), "end": (20, 45), "min_duration": 90, "priority": 3},
    "Timothy": {"location": "Pacific Heights", "start": (12, 0), "end": (18, 0), "min_duration": 90, "priority": 2},
    "Ashley": {"location": "Golden Gate Park", "start": (20, 45), "end": (21, 45), "min_duration": 60, "priority": 2},
    "Kevin": {"location": "Chinatown", "start": (12, 0), "end": (19, 0), "min_duration": 30, "priority": 1},
    "Betty": {"location": "Richmond District", "start": (13, 15), "end": (15, 45), "min_duration": 30, "priority": 1},
}

def time_to_minutes(h, m):
    return h * 60 + m - 540  # 9:00 AM is 540 minutes

def minutes_to_time(m):
    total = m + 540
    h = total // 60
    m = total % 60
    return f"{h:02d}:{m:02d}"

def solve_scheduling():
    s = Optimize()
    
    # Create meeting variables
    meetings = {}
    for name in friends:
        start = Int(f"start_{name}")
        end = Int(f"end_{name}")
        meetings[name] = {
            "start": start,
            "end": end,
            "location": friends[name]["location"],
            "priority": friends[name]["priority"]
        }
        # Hard constraints
        s.add(start >= time_to_minutes(*friends[name]["start"]))
        s.add(end <= time_to_minutes(*friends[name]["end"]))
        s.add(end - start >= friends[name]["min_duration"])
        s.add(start >= 0)
        s.add(end >= 0)

    # Initial location constraint
    first_meeting = [name for name in meetings if friends[name]["start"] == min(f["start"] for f in friends.values())][0]
    s.add(meetings[first_meeting]["start"] >= travel_times.get(("Mission District", meetings[first_meeting]["location"]), 0))

    # Meeting ordering constraints
    names = list(meetings.keys())
    for i in range(len(names)):
        for j in range(i+1, len(names)):
            loc1 = meetings[names[i]]["location"]
            loc2 = meetings[names[j]]["location"]
            travel = travel_times.get((loc1, loc2), 0)
            s.add(Or(
                meetings[names[j]]["start"] >= meetings[names[i]]["end"] + travel,
                meetings[names[i]]["start"] >= meetings[names[j]]["end"] + travel
            ))

    # Optimization: maximize priority sum
    priority_sum = sum(If(meetings[name]["start"] >= 0, meetings[name]["priority"], 0) for name in meetings)
    s.maximize(priority_sum)

    if s.check() == sat:
        m = s.model()
        itinerary = []
        for name in meetings:
            start = m[meetings[name]["start"]].as_long()
            end = m[meetings[name]["end"]].as_long()
            if start >= 0:  # Only include scheduled meetings
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": minutes_to_time(start),
                    "end_time": minutes_to_time(end),
                    "location": meetings[name]["location"]
                })
        # Sort by start time
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        # Try relaxing constraints if no solution found
        print("No solution found with current constraints. Trying relaxed version...")
        relaxed_solver = Solver()
        for name in meetings:
            relaxed_solver.add(meetings[name]["start"] >= time_to_minutes(*friends[name]["start"]))
            relaxed_solver.add(meetings[name]["end"] <= time_to_minutes(*friends[name]["end"]))
            relaxed_solver.add(meetings[name]["end"] - meetings[name]["start"] >= friends[name]["min_duration"] // 2)
        
        if relaxed_solver.check() == sat:
            m = relaxed_solver.model()
            itinerary = []
            for name in meetings:
                start = m[meetings[name]["start"]].as_long()
                end = m[meetings[name]["end"]].as_long()
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": minutes_to_time(start),
                    "end_time": minutes_to_time(end),
                    "location": meetings[name]["location"],
                    "note": "relaxed constraints"
                })
            itinerary.sort(key=lambda x: x["start_time"])
            return {"itinerary": itinerary, "note": "Used relaxed constraints (reduced meeting durations)"}
        else:
            return {"itinerary": [], "error": "No feasible schedule found even with relaxed constraints"}

result = solve_scheduling()
print(json.dumps(result, indent=2))