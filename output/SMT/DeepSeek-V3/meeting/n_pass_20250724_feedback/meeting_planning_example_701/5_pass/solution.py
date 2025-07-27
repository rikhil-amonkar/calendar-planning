from z3 import *
import json

def solve_scheduling_problem():
    s = Solver()

    # Define friends data
    friends = {
        "Lisa": {"location": "The Castro", "available_start": 19*60+15, "available_end": 21*60+15, "min_duration": 120},
        "Daniel": {"location": "Nob Hill", "available_start": 8*60+15, "available_end": 11*60, "min_duration": 15},
        "Elizabeth": {"location": "Presidio", "available_start": 21*60+15, "available_end": 22*60+15, "min_duration": 45},
        "Steven": {"location": "Marina District", "available_start": 16*60+30, "available_end": 20*60+45, "min_duration": 90},
        "Timothy": {"location": "Pacific Heights", "available_start": 12*60, "available_end": 18*60, "min_duration": 90},
        "Ashley": {"location": "Golden Gate Park", "available_start": 20*60+45, "available_end": 21*60+45, "min_duration": 60},
        "Kevin": {"location": "Chinatown", "available_start": 12*60, "available_end": 19*60, "min_duration": 30},
        "Betty": {"location": "Richmond District", "available_start": 13*60+15, "available_end": 15*60+45, "min_duration": 30}
    }

    # Travel times between locations
    travel_times = {
        "Mission District": {"The Castro": 7, "Nob Hill": 12, "Presidio": 25, "Marina District": 19, 
                            "Pacific Heights": 16, "Golden Gate Park": 17, "Chinatown": 16, "Richmond District": 20},
        "The Castro": {"Mission District": 7, "Nob Hill": 16, "Presidio": 20, "Marina District": 21,
                      "Pacific Heights": 16, "Golden Gate Park": 11, "Chinatown": 22, "Richmond District": 16},
        "Nob Hill": {"Mission District": 13, "The Castro": 17, "Presidio": 17, "Marina District": 11,
                     "Pacific Heights": 8, "Golden Gate Park": 17, "Chinatown": 6, "Richmond District": 14},
        "Presidio": {"Mission District": 26, "The Castro": 21, "Nob Hill": 18, "Marina District": 11,
                    "Pacific Heights": 11, "Golden Gate Park": 12, "Chinatown": 21, "Richmond District": 7},
        "Marina District": {"Mission District": 20, "The Castro": 22, "Nob Hill": 12, "Presidio": 10,
                           "Pacific Heights": 7, "Golden Gate Park": 18, "Chinatown": 15, "Richmond District": 11},
        "Pacific Heights": {"Mission District": 15, "The Castro": 16, "Nob Hill": 8, "Presidio": 11,
                           "Marina District": 6, "Golden Gate Park": 15, "Chinatown": 11, "Richmond District": 12},
        "Golden Gate Park": {"Mission District": 17, "The Castro": 13, "Nob Hill": 20, "Presidio": 11,
                            "Marina District": 16, "Pacific Heights": 16, "Chinatown": 23, "Richmond District": 7},
        "Chinatown": {"Mission District": 17, "The Castro": 22, "Nob Hill": 9, "Presidio": 19,
                     "Marina District": 12, "Pacific Heights": 10, "Golden Gate Park": 23, "Richmond District": 20},
        "Richmond District": {"Mission District": 20, "The Castro": 16, "Nob Hill": 17, "Presidio": 7,
                             "Marina District": 9, "Pacific Heights": 10, "Golden Gate Park": 9, "Chinatown": 20}
    }

    # Create variables for meeting times
    meeting_starts = {name: Int(f'start_{name}') for name in friends}
    meeting_ends = {name: Int(f'end_{name}') for name in friends}

    # Add basic constraints for each friend
    for name in friends:
        friend = friends[name]
        s.add(meeting_starts[name] >= friend["available_start"])
        s.add(meeting_ends[name] <= friend["available_end"])
        s.add(meeting_ends[name] - meeting_starts[name] >= friend["min_duration"])

    # Create variables to represent the meeting order
    meeting_order = {name: Int(f'order_{name}') for name in friends}
    s.add(Distinct([meeting_order[name] for name in friends]))
    for name in friends:
        s.add(meeting_order[name] >= 0)
        s.add(meeting_order[name] < len(friends))

    # Add travel time constraints between consecutive meetings
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                # If meeting1 comes before meeting2 in the order
                s.add(Implies(
                    meeting_order[name1] + 1 == meeting_order[name2],
                    meeting_starts[name2] >= meeting_ends[name1] + travel_times[friends[name1]["location"]][friends[name2]["location"]]
                ))

    # Starting point - arrive at Mission District at 9:00 AM (540 minutes)
    first_meeting = [name for name in friends if meeting_order[name] == 0][0]
    s.add(meeting_starts[first_meeting] >= 9*60 + travel_times["Mission District"][friends[first_meeting]["location"]])

    # Try to solve
    if s.check() == sat:
        model = s.model()
        # Get the order of meetings
        ordered_meetings = sorted(friends.keys(), key=lambda x: model.eval(meeting_order[x]).as_long())
        
        itinerary = []
        for name in ordered_meetings:
            start = model.eval(meeting_starts[name]).as_long()
            end = model.eval(meeting_ends[name]).as_long()
            start_time = f"{start//60:02d}:{start%60:02d}"
            end_time = f"{end//60:02d}:{end%60:02d}"
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": start_time,
                "end_time": end_time
            })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

result = solve_scheduling_problem()
print(json.dumps(result, indent=2))