from z3 import *
import json

def solve_scheduling_problem():
    s = Solver()

    # Define people and their constraints
    people = {
        "Emily": {"location": "Pacific Heights", "available_start": "9:15", "available_end": "13:45", "min_duration": 120},
        "Helen": {"location": "North Beach", "available_start": "13:45", "available_end": "18:45", "min_duration": 30},
        "Kimberly": {"location": "Golden Gate Park", "available_start": "18:45", "available_end": "21:15", "min_duration": 75},
        "James": {"location": "Embarcadero", "available_start": "10:30", "available_end": "11:30", "min_duration": 30},
        "Linda": {"location": "Haight-Ashbury", "available_start": "7:30", "available_end": "19:15", "min_duration": 15},
        "Paul": {"location": "Fisherman's Wharf", "available_start": "14:45", "available_end": "18:45", "min_duration": 90},
        "Anthony": {"location": "Mission District", "available_start": "8:00", "available_end": "14:45", "min_duration": 105},
        "Nancy": {"location": "Alamo Square", "available_start": "8:30", "available_end": "13:45", "min_duration": 120},
        "William": {"location": "Bayview", "available_start": "17:30", "available_end": "20:30", "min_duration": 120},
        "Margaret": {"location": "Richmond District", "available_start": "15:15", "available_end": "18:15", "min_duration": 45}
    }

    # Convert time to minutes
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Travel times dictionary
    travel_times = {
        ("Russian Hill", "Pacific Heights"): 7,
        ("Russian Hill", "North Beach"): 5,
        # ... (include all other travel times from previous code)
    }

    # Create meeting variables
    meetings = {}
    for person in people:
        meetings[person] = {
            "start": Int(f"start_{person}"),
            "end": Int(f"end_{person}"),
            "location": people[person]["location"]
        }

    # Add basic constraints
    for person in people:
        data = people[person]
        start = time_to_minutes(data["available_start"])
        end = time_to_minutes(data["available_end"])
        duration = data["min_duration"]

        s.add(meetings[person]["start"] >= start)
        s.add(meetings[person]["end"] <= end)
        s.add(meetings[person]["end"] - meetings[person]["start"] >= duration)

    # Current location is Russian Hill at 9:00 AM (540 minutes)
    current_time = 540
    current_location = "Russian Hill"

    # Create meeting order variables
    meeting_order = {person: Int(f"order_{person}") for person in people}
    for person in people:
        s.add(meeting_order[person] >= 0)
        s.add(meeting_order[person] < len(people))

    # All meeting orders must be distinct
    s.add(Distinct([meeting_order[person] for person in people]))

    # Add travel time constraints between consecutive meetings
    for p1 in people:
        for p2 in people:
            if p1 != p2:
                # If p1 comes before p2 in the order
                s.add(Implies(
                    meeting_order[p1] < meeting_order[p2],
                    meetings[p1]["end"] + travel_times.get(
                        (meetings[p1]["location"], meetings[p2]["location"]), 0
                    ) <= meetings[p2]["start"]
                ))

    # Try to solve
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for person in people:
            start = model[meetings[person]["start"]].as_long()
            end = model[meetings[person]["end"]].as_long()
            itinerary.append({
                "action": "meet",
                "person": person,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end),
                "location": meetings[person]["location"]
            })
        # Sort by start time
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid schedule found"}

solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))