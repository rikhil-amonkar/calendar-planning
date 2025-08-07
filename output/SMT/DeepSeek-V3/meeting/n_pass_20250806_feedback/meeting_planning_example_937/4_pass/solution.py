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
        "Sunset District": {
            "Russian Hill": 24,
            "Union Square": 30,
            "Nob Hill": 27,
            "Marina District": 21,
            "Richmond District": 12,
            "Financial District": 30,
            "Embarcadero": 30,
            "The Castro": 17,
            "Alamo Square": 17,
            "Presidio": 16
        },
        "Union Square": {
            "Russian Hill": 13,
            "Sunset District": 27,
            "Nob Hill": 9,
            "Marina District": 18,
            "Richmond District": 20,
            "Financial District": 9,
            "Embarcadero": 11,
            "The Castro": 17,
            "Alamo Square": 15,
            "Presidio": 24
        },
        "Nob Hill": {
            "Russian Hill": 5,
            "Sunset District": 24,
            "Union Square": 7,
            "Marina District": 11,
            "Richmond District": 14,
            "Financial District": 9,
            "Embarcadero": 9,
            "The Castro": 17,
            "Alamo Square": 11,
            "Presidio": 17
        },
        "Marina District": {
            "Russian Hill": 8,
            "Sunset District": 19,
            "Union Square": 16,
            "Nob Hill": 12,
            "Richmond District": 11,
            "Financial District": 17,
            "Embarcadero": 14,
            "The Castro": 22,
            "Alamo Square": 15,
            "Presidio": 10
        },
        "Richmond District": {
            "Russian Hill": 13,
            "Sunset District": 11,
            "Union Square": 21,
            "Nob Hill": 17,
            "Marina District": 9,
            "Financial District": 22,
            "Embarcadero": 19,
            "The Castro": 16,
            "Alamo Square": 13,
            "Presidio": 7
        },
        "Financial District": {
            "Russian Hill": 11,
            "Sunset District": 30,
            "Union Square": 9,
            "Nob Hill": 8,
            "Marina District": 15,
            "Richmond District": 21,
            "Embarcadero": 4,
            "The Castro": 20,
            "Alamo Square": 17,
            "Presidio": 22
        },
        "Embarcadero": {
            "Russian Hill": 8,
            "Sunset District": 30,
            "Union Square": 10,
            "Nob Hill": 10,
            "Marina District": 12,
            "Richmond District": 21,
            "Financial District": 5,
            "The Castro": 25,
            "Alamo Square": 19,
            "Presidio": 20
        },
        "The Castro": {
            "Russian Hill": 18,
            "Sunset District": 17,
            "Union Square": 19,
            "Nob Hill": 16,
            "Marina District": 21,
            "Richmond District": 16,
            "Financial District": 21,
            "Embarcadero": 22,
            "Alamo Square": 8,
            "Presidio": 20
        },
        "Alamo Square": {
            "Russian Hill": 13,
            "Sunset District": 16,
            "Union Square": 14,
            "Nob Hill": 11,
            "Marina District": 15,
            "Richmond District": 11,
            "Financial District": 17,
            "Embarcadero": 16,
            "The Castro": 8,
            "Presidio": 17
        },
        "Presidio": {
            "Russian Hill": 14,
            "Sunset District": 15,
            "Union Square": 22,
            "Nob Hill": 18,
            "Marina District": 11,
            "Richmond District": 7,
            "Financial District": 23,
            "Embarcadero": 20,
            "The Castro": 21,
            "Alamo Square": 19
        }
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

    # Convert minutes back to time string
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
    # We'll model this as a sequence where each meeting must account for travel time from the previous one
    # First, create an ordering of meetings
    order = [Int(f"order_{i}") for i in range(len(meetings))]
    s.add(Distinct(order))
    for i in range(len(meetings)):
        s.add(And(order[i] >= 0, order[i] < len(meetings)))

    # Add constraints for consecutive meetings in the order
    for i in range(len(meetings) - 1):
        for j in range(i + 1, len(meetings)):
            # If meeting i comes before meeting j in the order, then meeting i must finish before meeting j starts
            s.add(Implies(
                order[i] < order[j],
                meetings[i]["end"] + travel_times[meetings[i]["location"]][meetings[j]["location"]] <= meetings[j]["start"]
            ))

    # Ensure all meetings are scheduled
    for meeting in meetings:
        s.add(meeting["start"] >= 0)

    # Try to find a solution
    if s.check() == sat:
        model = s.model()
        # Create a list of meetings with their actual times
        scheduled_meetings = []
        for meeting in meetings:
            start = model[meeting["start"]].as_long()
            end = model[meeting["end"]].as_long()
            scheduled_meetings.append({
                "action": "meet",
                "person": meeting["name"],
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        # Sort by start time
        scheduled_meetings.sort(key=lambda x: x["start_time"])
        return {"itinerary": scheduled_meetings}
    else:
        # If no solution found, try relaxing constraints
        # First, try removing the longest meeting (Patricia)
        print("No solution found with all meetings. Trying to relax constraints...")
        s.reset()
        # Remove Patricia's meeting
        friends = [f for f in friends if f["name"] != "Patricia"]
        # Try again with the remaining meetings
        return solve_scheduling_with_relaxed_constraints(friends, travel_times)

def solve_scheduling_with_relaxed_constraints(friends, travel_times):
    # Similar to solve_scheduling but with relaxed constraints
    s = Solver()

    # Convert time to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(h, m):
        return h * 60 + m - 540  # 9:00 AM is 540 minutes

    # Convert minutes back to time string
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

    for i in range(len(meetings) - 1):
        for j in range(i + 1, len(meetings)):
            s.add(Implies(
                order[i] < order[j],
                meetings[i]["end"] + travel_times[meetings[i]["location"]][meetings[j]["location"]] <= meetings[j]["start"]
            ))

    for meeting in meetings:
        s.add(meeting["start"] >= 0)

    if s.check() == sat:
        model = s.model()
        scheduled_meetings = []
        for meeting in meetings:
            start = model[meeting["start"]].as_long()
            end = model[meeting["end"]].as_long()
            scheduled_meetings.append({
                "action": "meet",
                "person": meeting["name"],
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        scheduled_meetings.sort(key=lambda x: x["start_time"])
        return {"itinerary": scheduled_meetings}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling()
print("SOLUTION:")
print(json.dumps(solution, indent=2))