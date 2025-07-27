from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver with optimization
    opt = Optimize()

    # Define locations and symmetric travel times
    locations = [
        "Embarcadero", "Fisherman's Wharf", "Financial District", "Russian Hill", "Marina District",
        "Richmond District", "Pacific Heights", "Haight-Ashbury", "Presidio", "Nob Hill", "The Castro"
    ]

    # Travel times matrix (minutes)
    travel_times = {
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "Marina District"): 12,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Pacific Heights"): 11,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "The Castro"): 25,
        # Add all other symmetric travel times here...
    }

    # Friends data with constraints
    friends = [
        {"name": "Stephanie", "location": "Fisherman's Wharf", "start": "15:30", "end": "22:00", "duration": 30},
        {"name": "Lisa", "location": "Financial District", "start": "10:45", "end": "17:15", "duration": 15},
        {"name": "Melissa", "location": "Russian Hill", "start": "17:00", "end": "21:45", "duration": 120},
        {"name": "Betty", "location": "Marina District", "start": "10:45", "end": "14:15", "duration": 60},
        {"name": "Sarah", "location": "Richmond District", "start": "16:15", "end": "19:30", "duration": 105},
        {"name": "Daniel", "location": "Pacific Heights", "start": "18:30", "end": "21:45", "duration": 60},
        {"name": "Joshua", "location": "Haight-Ashbury", "start": "09:00", "end": "15:30", "duration": 15},
        {"name": "Joseph", "location": "Presidio", "start": "07:00", "end": "13:00", "duration": 45},
        {"name": "Andrew", "location": "Nob Hill", "start": "19:45", "end": "22:00", "duration": 105},
        {"name": "John", "location": "The Castro", "start": "13:15", "end": "19:45", "duration": 45},
    ]

    # Time conversion functions
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm - 540  # 9:00 AM is 540 minutes

    def minutes_to_time(minutes):
        total_minutes = 540 + minutes
        hh = total_minutes // 60
        mm = total_minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Create meeting variables and constraints
    meeting_vars = []
    for friend in friends:
        start = Int(f"start_{friend['name']}")
        end = Int(f"end_{friend['name']}")
        duration = friend['duration']
        meeting_vars.append((friend, start, end))

        # Basic constraints
        opt.add(start >= time_to_minutes(friend['start']))
        opt.add(end <= time_to_minutes(friend['end']))
        opt.add(end == start + duration)

    # Add travel time constraints
    for i in range(len(meeting_vars)):
        for j in range(i + 1, len(meeting_vars)):
            f1, s1, e1 = meeting_vars[i]
            f2, s2, e2 = meeting_vars[j]
            
            loc1 = f1['location']
            loc2 = f2['location']
            travel = travel_times.get((loc1, loc2), travel_times.get((loc2, loc1), 0))
            
            opt.add(Or(
                e1 + travel <= s2,
                e2 + travel <= s1
            ))

    # Starting point constraint
    first_meeting_start = Int("first_start")
    opt.add(first_meeting_start >= 0)
    for friend, start, _ in meeting_vars:
        loc = friend['location']
        travel = travel_times.get(("Embarcadero", loc), travel_times.get((loc, "Embarcadero"), 0))
        opt.add(Or(start >= first_meeting_start + travel, start == 0))

    # Optimization goal - maximize number of meetings
    meeting_counts = [If(And(s >= 0, e > s), 1, 0) for _, s, e in meeting_vars]
    total_meetings = sum(meeting_counts)
    opt.maximize(total_meetings)

    # Solve and format results
    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        for friend, start, end in meeting_vars:
            s = m.evaluate(start).as_long()
            e = m.evaluate(end).as_long()
            if s >= 0 and e > s:
                itinerary.append({
                    "action": "meet",
                    "person": friend["name"],
                    "start_time": minutes_to_time(s),
                    "end_time": minutes_to_time(e)
                })
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        print("Failed to find a valid schedule")
        return {"itinerary": []}

# Execute and print results
result = solve_scheduling()
print(json.dumps(result, indent=2))