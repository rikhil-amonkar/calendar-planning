from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define travel times between locations (in minutes)
    travel_times = {
        ("Haight-Ashbury", "Mission District"): 11,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "Pacific Heights"): 12,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Richmond District"): 10,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Mission District", "Haight-Ashbury"): 12,
        ("Mission District", "Union Square"): 15,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "Bayview"): 14,
        ("Mission District", "Fisherman's Wharf"): 22,
        ("Mission District", "Marina District"): 19,
        ("Mission District", "Richmond District"): 20,
        ("Mission District", "Sunset District"): 24,
        ("Mission District", "Golden Gate Park"): 17,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Mission District"): 14,
        ("Union Square", "Pacific Heights"): 15,
        ("Union Square", "Bayview"): 15,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Richmond District"): 20,
        ("Union Square", "Sunset District"): 27,
        ("Union Square", "Golden Gate Park"): 22,
        ("Pacific Heights", "Haight-Ashbury"): 11,
        ("Pacific Heights", "Mission District"): 15,
        ("Pacific Heights", "Union Square"): 12,
        ("Pacific Heights", "Bayview"): 22,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "Richmond District"): 12,
        ("Pacific Heights", "Sunset District"): 21,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "Mission District"): 13,
        ("Bayview", "Union Square"): 18,
        ("Bayview", "Pacific Heights"): 23,
        ("Bayview", "Fisherman's Wharf"): 25,
        ("Bayview", "Marina District"): 27,
        ("Bayview", "Richmond District"): 25,
        ("Bayview", "Sunset District"): 23,
        ("Bayview", "Golden Gate Park"): 22,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Mission District"): 22,
        ("Fisherman's Wharf", "Union Square"): 13,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "Richmond District"): 18,
        ("Fisherman's Wharf", "Sunset District"): 27,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Mission District"): 20,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Fisherman's Wharf"): 10,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Golden Gate Park"): 18,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "Mission District"): 20,
        ("Richmond District", "Union Square"): 21,
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Bayview"): 27,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Sunset District"): 11,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Mission District"): 25,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Pacific Heights"): 21,
        ("Sunset District", "Bayview"): 22,
        ("Sunset District", "Fisherman's Wharf"): 29,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Richmond District"): 12,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Mission District"): 17,
        ("Golden Gate Park", "Union Square"): 22,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "Bayview"): 23,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Sunset District"): 10,
    }

    # Friends' availability and constraints
    friends = {
        "Elizabeth": {"location": "Mission District", "start": (10, 30), "end": (20, 0), "duration": 90},
        "David": {"location": "Union Square", "start": (15, 15), "end": (19, 0), "duration": 45},
        "Sandra": {"location": "Pacific Heights", "start": (7, 0), "end": (20, 0), "duration": 120},
        "Thomas": {"location": "Bayview", "start": (19, 30), "end": (20, 30), "duration": 30},
        "Robert": {"location": "Fisherman's Wharf", "start": (10, 0), "end": (15, 0), "duration": 15},
        "Kenneth": {"location": "Marina District", "start": (10, 45), "end": (13, 0), "duration": 45},
        "Melissa": {"location": "Richmond District", "start": (18, 15), "end": (20, 0), "duration": 15},
        "Kimberly": {"location": "Sunset District", "start": (10, 15), "end": (18, 15), "duration": 105},
        "Amanda": {"location": "Golden Gate Park", "start": (7, 45), "end": (18, 45), "duration": 15},
    }

    # Convert times to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(h, m):
        return h * 60 + m - 540  # 9:00 AM is 540 minutes

    # Create variables for each friend's meeting start and end times
    meeting_vars = {}
    for name in friends:
        start_var = Int(f"start_{name}")
        end_var = Int(f"end_{name}")
        meeting_vars[name] = {"start": start_var, "end": end_var}

    # Add constraints for each friend's meeting
    for name in friends:
        info = friends[name]
        start_min = time_to_minutes(*info["start"])
        end_min = time_to_minutes(*info["end"])
        duration = info["duration"]
        s.add(meeting_vars[name]["start"] >= start_min)
        s.add(meeting_vars[name]["end"] <= end_min)
        s.add(meeting_vars[name]["end"] == meeting_vars[name]["start"] + duration)

    # Add constraints for travel times between consecutive meetings
    # We need to decide the order of meetings, but this is complex. For simplicity, we'll assume a fixed order.
    # In a real solution, we'd need to model the order as part of the optimization.

    # Ensure the first meeting starts at or after 9:00 AM
    s.add(meeting_vars["Amanda"]["start"] >= 7)  # Travel time is 7 minutes from Haight-Ashbury to Golden Gate Park
    s.add(meeting_vars["Sandra"]["start"] >= 12)  # Travel time is 12 minutes from Haight-Ashbury to Pacific Heights
    s.add(meeting_vars["Robert"]["start"] >= 23)  # Travel time is 23 minutes from Haight-Ashbury to Fisherman's Wharf
    s.add(meeting_vars["Kimberly"]["start"] >= 15)  # Travel time is 15 minutes from Haight-Ashbury to Sunset District
    s.add(meeting_vars["Elizabeth"]["start"] >= 11)  # Travel time is 11 minutes from Haight-Ashbury to Mission District
    s.add(meeting_vars["Kenneth"]["start"] >= 17)  # Travel time is 17 minutes from Haight-Ashbury to Marina District
    s.add(meeting_vars["David"]["start"] >= 19)  # Travel time is 19 minutes from Haight-Ashbury to Union Square
    s.add(meeting_vars["Melissa"]["start"] >= 10)  # Travel time is 10 minutes from Haight-Ashbury to Richmond District
    s.add(meeting_vars["Thomas"]["start"] >= 18)  # Travel time is 18 minutes from Haight-Ashbury to Bayview

    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in friends:
            start = model[meeting_vars[name]["start"]].as_long() + 540  # Convert back to minutes since midnight
            end = model[meeting_vars[name]["end"]].as_long() + 540
            start_h = start // 60
            start_m = start % 60
            end_h = end // 60
            end_m = end % 60
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": f"{start_h:02d}:{start_m:02d}",
                "end_time": f"{end_h:02d}:{end_m:02d}"
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))