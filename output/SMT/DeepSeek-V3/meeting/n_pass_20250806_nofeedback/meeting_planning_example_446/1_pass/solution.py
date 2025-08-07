from z3 import *
import datetime

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define districts and friends' information
    districts = {
        "Richmond": 0,
        "Marina": 1,
        "Chinatown": 2,
        "Financial": 3,
        "Bayview": 4,
        "Union Square": 5
    }

    friends = {
        "Kimberly": {"district": "Marina", "start": 13.25, "end": 16.75, "duration": 0.25},
        "Robert": {"district": "Chinatown", "start": 12.25, "end": 20.25, "duration": 0.25},
        "Rebecca": {"district": "Financial", "start": 13.25, "end": 16.75, "duration": 1.25},
        "Margaret": {"district": "Bayview", "start": 9.5, "end": 13.5, "duration": 0.5},
        "Kenneth": {"district": "Union Square", "start": 19.5, "end": 21.25, "duration": 1.25}
    }

    # Travel times matrix (in hours)
    travel_times = [
        [0, 9/60, 20/60, 22/60, 26/60, 21/60],
        [11/60, 0, 16/60, 17/60, 27/60, 16/60],
        [20/60, 12/60, 0, 5/60, 22/60, 7/60],
        [21/60, 15/60, 5/60, 0, 19/60, 9/60],
        [25/60, 25/60, 18/60, 19/60, 0, 17/60],
        [20/60, 18/60, 7/60, 9/60, 15/60, 0]
    ]

    # Variables for each meeting: start and end times
    meet_vars = {}
    for friend in friends:
        meet_vars[friend] = {
            "start": Real(f"{friend}_start"),
            "end": Real(f"{friend}_end"),
            "district": districts[friends[friend]["district"]]
        }

    # Constraints for each meeting
    for friend in friends:
        info = friends[friend]
        s.add(meet_vars[friend]["start"] >= info["start"])
        s.add(meet_vars[friend]["end"] <= info["end"])
        s.add(meet_vars[friend]["end"] - meet_vars[friend]["start"] >= info["duration"])

    # Initial position: Richmond at 9:00 AM (9.0)
    current_time = 9.0
    current_district = districts["Richmond"]

    # Order of meetings to try (this can be adjusted for optimization)
    meeting_order = ["Margaret", "Robert", "Kimberly", "Rebecca", "Kenneth"]

    # Ensure meetings are in feasible order with travel times
    for i in range(len(meeting_order)):
        friend = meeting_order[i]
        s.add(meet_vars[friend]["start"] >= current_time + travel_times[current_district][meet_vars[friend]["district"]])
        current_time = meet_vars[friend]["end"]
        current_district = meet_vars[friend]["district"]

    # Ensure no overlapping meetings
    for i in range(len(meeting_order)):
        for j in range(i + 1, len(meeting_order)):
            f1 = meeting_order[i]
            f2 = meeting_order[j]
            s.add(Or(
                meet_vars[f1]["end"] <= meet_vars[f2]["start"],
                meet_vars[f2]["end"] <= meet_vars[f1]["start"]
            ))

    # Check if a solution exists
    if s.check() == sat:
        model = s.model()
        itinerary = []

        # Collect all meetings with their times
        for friend in friends:
            start = model[meet_vars[friend]["start"]]
            end = model[meet_vars[friend]["end"]]
            start_time = float(start.as_fraction())
            end_time = float(end.as_fraction())

            # Convert fractional hours to HH:MM format
            def to_time_str(frac_hours):
                hours = int(frac_hours)
                minutes = int((frac_hours - hours) * 60)
                return f"{hours:02d}:{minutes:02d}"

            itinerary.append({
                "action": "meet",
                "person": friend,
                "start_time": to_time_str(start_time),
                "end_time": to_time_str(end_time)
            })

        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])

        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve and print the solution
solution = solve_scheduling()
print(solution)