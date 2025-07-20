from z3 import *
import json

def solve_scheduling():
    s = Optimize()

    # Define friends with their constraints
    friends = [
        {"name": "Karen", "location": "Haight-Ashbury", "start": 21.0, "end": 21.75, "duration": 0.75},
        {"name": "Jessica", "location": "Nob Hill", "start": 13.75, "end": 21.0, "duration": 1.5},
        {"name": "Brian", "location": "Russian Hill", "start": 15.5, "end": 21.75, "duration": 1.0},
        {"name": "Kenneth", "location": "North Beach", "start": 9.75, "end": 21.0, "duration": 0.5},
        {"name": "Jason", "location": "Chinatown", "start": 8.25, "end": 11.75, "duration": 1.25},
        {"name": "Stephanie", "location": "Union Square", "start": 14.75, "end": 18.75, "duration": 1.75},
        {"name": "Kimberly", "location": "Embarcadero", "start": 9.75, "end": 19.5, "duration": 1.25},
        {"name": "Steven", "location": "Financial District", "start": 7.25, "end": 21.25, "duration": 1.0},
        {"name": "Mark", "location": "Marina District", "start": 10.25, "end": 13.0, "duration": 1.25}
    ]

    # Complete travel times between all locations (in hours)
    travel_times = {
        "Presidio": {
            "Haight-Ashbury": 15/60, "Nob Hill": 18/60, "Russian Hill": 14/60,
            "North Beach": 18/60, "Chinatown": 21/60, "Union Square": 22/60,
            "Embarcadero": 20/60, "Financial District": 23/60, "Marina District": 11/60
        },
        "Haight-Ashbury": {
            "Presidio": 15/60, "Nob Hill": 15/60, "Russian Hill": 17/60,
            "North Beach": 19/60, "Chinatown": 19/60, "Union Square": 19/60,
            "Embarcadero": 20/60, "Financial District": 21/60, "Marina District": 17/60
        },
        "Nob Hill": {
            "Presidio": 17/60, "Haight-Ashbury": 13/60, "Russian Hill": 5/60,
            "North Beach": 8/60, "Chinatown": 6/60, "Union Square": 7/60,
            "Embarcadero": 9/60, "Financial District": 9/60, "Marina District": 11/60
        },
        "Russian Hill": {
            "Presidio": 14/60, "Haight-Ashbury": 17/60, "Nob Hill": 5/60,
            "North Beach": 5/60, "Chinatown": 9/60, "Union Square": 10/60,
            "Embarcadero": 8/60, "Financial District": 11/60, "Marina District": 7/60
        },
        "North Beach": {
            "Presidio": 17/60, "Haight-Ashbury": 18/60, "Nob Hill": 7/60,
            "Russian Hill": 4/60, "Chinatown": 6/60, "Union Square": 7/60,
            "Embarcadero": 6/60, "Financial District": 8/60, "Marina District": 9/60
        },
        "Chinatown": {
            "Presidio": 19/60, "Haight-Ashbury": 19/60, "Nob Hill": 9/60,
            "Russian Hill": 7/60, "North Beach": 3/60, "Union Square": 7/60,
            "Embarcadero": 5/60, "Financial District": 5/60, "Marina District": 12/60
        },
        "Union Square": {
            "Presidio": 24/60, "Haight-Ashbury": 18/60, "Nob Hill": 9/60,
            "Russian Hill": 13/60, "North Beach": 10/60, "Chinatown": 7/60,
            "Embarcadero": 11/60, "Financial District": 9/60, "Marina District": 18/60
        },
        "Embarcadero": {
            "Presidio": 20/60, "Haight-Ashbury": 21/60, "Nob Hill": 10/60,
            "Russian Hill": 8/60, "North Beach": 5/60, "Chinatown": 7/60,
            "Union Square": 10/60, "Financial District": 5/60, "Marina District": 12/60
        },
        "Financial District": {
            "Presidio": 22/60, "Haight-Ashbury": 19/60, "Nob Hill": 8/60,
            "Russian Hill": 11/60, "North Beach": 7/60, "Chinatown": 5/60,
            "Union Square": 9/60, "Embarcadero": 4/60, "Marina District": 15/60
        },
        "Marina District": {
            "Presidio": 10/60, "Haight-Ashbury": 16/60, "Nob Hill": 12/60,
            "Russian Hill": 8/60, "North Beach": 11/60, "Chinatown": 15/60,
            "Union Square": 16/60, "Embarcadero": 14/60, "Financial District": 17/60
        }
    }

    # Create variables for each meeting
    meeting_vars = []
    for friend in friends:
        start = Real(f"{friend['name']}_start")
        end = Real(f"{friend['name']}_end")
        met = Bool(f"met_{friend['name']}")
        
        # Meeting must be within availability window if it happens
        s.add(Implies(met, And(start >= friend["start"], end <= friend["end"])))
        s.add(Implies(met, end == start + friend["duration"]))
        
        meeting_vars.append({
            "name": friend["name"],
            "start": start,
            "end": end,
            "location": friend["location"],
            "met": met
        })

    # Starting point
    current_location = "Presidio"
    current_time = 9.0

    # Order meetings to ensure proper sequencing
    order = []
    for i in range(len(meeting_vars)):
        order.append(Int(f"order_{i}"))
        s.add(order[i] >= 0, order[i] < len(meeting_vars))
    
    # All orders must be unique
    s.add(Distinct(order))

    # Add sequencing constraints
    for i in range(len(meeting_vars)):
        for j in range(len(meeting_vars)):
            if i != j:
                # If meeting i comes before meeting j
                before = Bool(f"before_{i}_{j}")
                s.add(before == (order[i] < order[j]))
                
                # If both meetings happen, enforce travel time
                s.add(Implies(And(meeting_vars[i]["met"], meeting_vars[j]["met"], before),
                             meeting_vars[i]["end"] + travel_times[meeting_vars[i]["location"]][meeting_vars[j]["location"]] <= meeting_vars[j]["start"]))

    # Maximize number of meetings
    s.maximize(Sum([If(m["met"], 1, 0) for m in meeting_vars]))

    if s.check() == sat:
        m = s.model()
        itinerary = []
        scheduled_meetings = []
        
        # Collect all scheduled meetings
        for meeting in meeting_vars:
            if is_true(m[meeting["met"]]):
                start_val = m[meeting["start"]].as_fraction()
                end_val = m[meeting["end"]].as_fraction()
                start_time = float(start_val.numerator) / float(start_val.denominator)
                end_time = float(end_val.numerator) / float(end_val.denominator)
                
                start_hh = int(start_time)
                start_mm = int((start_time - start_hh) * 60)
                end_hh = int(end_time)
                end_mm = int((end_time - end_hh) * 60)
                
                scheduled_meetings.append({
                    "name": meeting["name"],
                    "start": start_time,
                    "start_time": f"{start_hh:02d}:{start_mm:02d}",
                    "end_time": f"{end_hh:02d}:{end_mm:02d}",
                    "order": m[order[meeting_vars.index(meeting)]].as_long()
                })
        
        # Sort by order
        scheduled_meetings.sort(key=lambda x: x["order"])
        
        # Build itinerary
        for meeting in scheduled_meetings:
            itinerary.append({
                "action": "meet",
                "person": meeting["name"],
                "start_time": meeting["start_time"],
                "end_time": meeting["end_time"]
            })
        
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

result = solve_scheduling()
print(json.dumps(result, indent=2))