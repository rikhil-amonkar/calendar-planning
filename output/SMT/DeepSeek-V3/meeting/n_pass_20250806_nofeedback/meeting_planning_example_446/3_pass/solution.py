from z3 import *
from datetime import datetime, timedelta

def solve_scheduling():
    s = Solver()

    # Districts mapping
    districts = {
        "Richmond": 0,
        "Marina": 1,
        "Chinatown": 2,
        "Financial": 3,
        "Bayview": 4,
        "Union Square": 5
    }

    # Friends' availability and requirements
    friends = {
        "Margaret": {"district": "Bayview", "start": 9.5, "end": 13.5, "duration": 0.5},
        "Robert": {"district": "Chinatown", "start": 12.25, "end": 20.25, "duration": 0.25},
        "Kimberly": {"district": "Marina", "start": 13.25, "end": 16.75, "duration": 0.25},
        "Rebecca": {"district": "Financial", "start": 13.25, "end": 16.75, "duration": 1.25},
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

    # Create variables for each meeting
    meet_vars = {}
    for friend in friends:
        meet_vars[friend] = {
            "start": Real(f"{friend}_start"),
            "end": Real(f"{friend}_end"),
            "district": districts[friends[friend]["district"]]
        }

    # Add basic constraints for each meeting
    for friend in friends:
        info = friends[friend]
        s.add(meet_vars[friend]["start"] >= info["start"])
        s.add(meet_vars[friend]["end"] <= info["end"])
        s.add(meet_vars[friend]["end"] - meet_vars[friend]["start"] >= info["duration"])

    # Define meeting order possibilities
    possible_orders = [
        ["Margaret", "Robert", "Kimberly", "Rebecca", "Kenneth"],
        ["Margaret", "Robert", "Rebecca", "Kimberly", "Kenneth"],
        ["Margaret", "Kimberly", "Robert", "Rebecca", "Kenneth"],
        ["Margaret", "Kimberly", "Rebecca", "Robert", "Kenneth"],
        ["Margaret", "Rebecca", "Robert", "Kimberly", "Kenneth"],
        ["Margaret", "Rebecca", "Kimberly", "Robert", "Kenneth"]
    ]

    # Try different meeting orders until we find a valid one
    for order in possible_orders:
        temp_solver = Solver()
        temp_solver.add(s.assertions())
        
        # Add travel time constraints for this order
        current_time = 9.0  # Start at 9:00 in Richmond
        current_district = districts["Richmond"]
        
        for i, friend in enumerate(order):
            # Must arrive at meeting with enough time
            temp_solver.add(meet_vars[friend]["start"] >= current_time + travel_times[current_district][meet_vars[friend]["district"]])
            
            # Update current time and location
            current_time = meet_vars[friend]["end"]
            current_district = meet_vars[friend]["district"]
            
            # Ensure no overlapping with previous meetings
            for prev_friend in order[:i]:
                temp_solver.add(Or(
                    meet_vars[prev_friend]["end"] + travel_times[meet_vars[prev_friend]["district"]][meet_vars[friend]["district"]] <= meet_vars[friend]["start"],
                    meet_vars[friend]["end"] + travel_times[meet_vars[friend]["district"]][meet_vars[prev_friend]["district"]] <= meet_vars[prev_friend]["start"]
                ))
        
        if temp_solver.check() == sat:
            model = temp_solver.model()
            itinerary = []
            
            for friend in friends:
                start = model[meet_vars[friend]["start"]]
                end = model[meet_vars[friend]["end"]]
                
                # Convert to HH:MM format
                def to_time(frac_hours):
                    hours = int(frac_hours)
                    minutes = int((frac_hours - hours) * 60)
                    return f"{hours:02d}:{minutes:02d}"
                
                itinerary.append({
                    "action": "meet",
                    "person": friend,
                    "start_time": to_time(float(start.as_fraction())),
                    "end_time": to_time(float(end.as_fraction())))
                })
            
            # Sort by start time
            itinerary.sort(key=lambda x: x["start_time"])
            return {"itinerary": itinerary}
    
    return {"itinerary": []}

solution = solve_scheduling()
print(solution)