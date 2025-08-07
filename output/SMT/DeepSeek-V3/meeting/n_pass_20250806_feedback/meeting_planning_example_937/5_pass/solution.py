from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define travel times (in minutes) from each location to another
    travel_times = {
        "Russian Hill": {
            "Sunset District": 23,
            "Union Square": 10,
            "Nob Hill": 5,
            "Marina District": 7,
            "Richmond District": 14,
            "Financial District": 11,
            "Embarcadero": 8,
            "The Castro": 21,
            "Alamo Square": 15,
            "Presidio": 14
        },
        # ... (rest of travel_times dictionary remains the same)
    }

    # Define friends' availability and constraints
    friends = [
        {"name": "David", "location": "Sunset District", "start": (9, 15), "end": (22, 0), "duration": 15},
        {"name": "Kenneth", "location": "Union Square", "start": (21, 15), "end": (21, 45), "duration": 15},
        {"name": "Patricia", "location": "Nob Hill", "start": (15, 0), "end": (19, 15), "duration": 120},
        {"name": "Mary", "location": "Marina District", "start": (14, 45), "end": (16, 45), "duration": 45},
        {"name": "Charles", "location": "Richmond District", "start": (17, 15), "end": (21, 0), "duration": 15},
        {"name": "Joshua", "location": "Financial District", "start": (14, 30), "end": (17, 15), "duration": 90},
        {"name": "Ronald", "location": "Embarcadero", "start": (18, 15), "end": (20, 45), "duration": 30},
        {"name": "George", "location": "The Castro", "start": (14, 15), "end": (19, 0), "duration": 105},
        {"name": "Kimberly", "location": "Alamo Square", "start": (9, 0), "end": (14, 30), "duration": 105},
        {"name": "William", "location": "Presidio", "start": (7, 0), "end": (12, 45), "duration": 60}
    ]

    # Convert time to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(h, m):
        return h * 60 + m - 540  # 9:00 AM is 540 minutes

    def minutes_to_time(m):
        total = m + 540
        h = total // 60
        m = total % 60
        return f"{h:02d}:{m:02d}"

    # Create variables for each meeting's start and end times
    meetings = []
    for friend in friends:
        start = Int(f"start_{friend['name']}")
        end = Int(f"end_{friend['name']}")
        available_start = time_to_minutes(*friend["start"])
        available_end = time_to_minutes(*friend["end"])
        meetings.append({
            "name": friend["name"],
            "location": friend["location"],
            "start": start,
            "end": end,
            "duration": friend["duration"],
            "available_start": available_start,
            "available_end": available_end
        })
        s.add(start >= available_start)
        s.add(end <= available_end)
        s.add(end == start + friend["duration"])

    # Add constraints for travel times between consecutive meetings
    order = [Int(f"order_{i}") for i in range(len(meetings))]
    s.add(Distinct(order))
    for i in range(len(meetings)):
        s.add(And(order[i] >= 0, order[i] < len(meetings)))

    # Starting point is Russian Hill at 9:00 AM (time = 0)
    starting_time = 0
    starting_location = "Russian Hill"

    # For each meeting, if it's first in the order, account for travel from starting location
    for i in range(len(meetings)):
        s.add(Implies(
            order[i] == 0,
            meetings[i]["start"] >= starting_time + travel_times[starting_location][meetings[i]["location"]]
        ))

    # For other meetings, account for travel from previous meeting
    for i in range(len(meetings)):
        for j in range(len(meetings)):
            if i != j:
                s.add(Implies(
                    order[j] == order[i] + 1,
                    meetings[j]["start"] >= meetings[i]["end"] + travel_times[meetings[i]["location"]][meetings[j]["location"]]
                ))

    # Ensure all meetings are scheduled
    for meeting in meetings:
        s.add(meeting["start"] >= 0)

    # Try to find a solution
    if s.check() == sat:
        model = s.model()
        # Create ordered list of meetings
        ordered_meetings = sorted(
            [(model[order[i]].as_long(), meetings[i]) for i in range(len(meetings))],
            key=lambda x: x[0]
        )
        
        itinerary = []
        for _, meeting in ordered_meetings:
            start = model[meeting["start"]].as_long()
            end = model[meeting["end"]].as_long()
            itinerary.append({
                "action": "meet",
                "person": meeting["name"],
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling()
print("SOLUTION:")
print(json.dumps(solution, indent=2))