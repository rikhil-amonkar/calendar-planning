from z3 import *
import json

def solve_scheduling():
    s = Optimize()  # Using Optimize instead of Solver to maximize meetings

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

    # Create variables and constraints for each meeting
    meeting_vars = []
    for friend in friends:
        start = Real(f"{friend['name']}_start")
        end = Real(f"{friend['name']}_end")
        s.add(start >= friend["start"])
        s.add(end <= friend["end"])
        s.add(end == start + friend["duration"])
        meeting_vars.append({
            "name": friend["name"],
            "start": start,
            "end": end,
            "location": friend["location"],
            "met": Int(f"met_{friend['name']}")  # 1 if meeting happens, 0 otherwise
        })
        s.add(Or(meeting_vars[-1]["met"] == 0, meeting_vars[-1]["met"] == 1))

    # Starting point
    current_location = "Presidio"
    current_time = 9.0

    # Ensure first meeting accounts for travel time
    for meeting in meeting_vars:
        s.add(Implies(meeting["met"] == 1,
                     meeting["start"] >= current_time + travel_times[current_location][meeting["location"]]))

    # No overlap between meetings and travel time constraints
    for i in range(len(meeting_vars)):
        for j in range(i + 1, len(meeting_vars)):
            loc_i = meeting_vars[i]["location"]
            loc_j = meeting_vars[j]["location"]
            s.add(Implies(And(meeting_vars[i]["met"] == 1, meeting_vars[j]["met"] == 1),
                         Or(
                            meeting_vars[i]["end"] + travel_times[loc_i][loc_j] <= meeting_vars[j]["start"],
                            meeting_vars[j]["end"] + travel_times[loc_j][loc_i] <= meeting_vars[i]["start"]
                         )))

    # Maximize the number of meetings
    s.maximize(Sum([m["met"] for m in meeting_vars]))

    if s.check() == sat:
        m = s.model()
        itinerary = []
        for meeting in meeting_vars:
            if m[meeting["met"]].as_long() == 1:
                start_val = m[meeting["start"]].as_fraction()
                end_val = m[meeting["end"]].as_fraction()
                start_time = float(start_val.numerator) / float(start_val.denominator)
                end_time = float(end_val.numerator) / float(end_val.denominator)
                
                start_hh = int(start_time)
                start_mm = int((start_time - start_hh) * 60)
                end_hh = int(end_time)
                end_mm = int((end_time - end_hh) * 60)
                
                itinerary.append({
                    "action": "meet",
                    "person": meeting["name"],
                    "start_time": f"{start_hh:02d}:{start_mm:02d}",
                    "end_time": f"{end_hh:02d}:{end_mm:02d}"
                })
        
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

result = solve_scheduling()
print(json.dumps(result, indent=2))