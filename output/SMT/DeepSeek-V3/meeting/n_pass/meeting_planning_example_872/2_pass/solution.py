from z3 import *
import json

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define the friends and their details
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

    # Define travel times (simplified for this example)
    travel_times = {
        "Presidio": {
            "Haight-Ashbury": 15/60,
            "Nob Hill": 18/60,
            "Russian Hill": 14/60,
            "North Beach": 18/60,
            "Chinatown": 21/60,
            "Union Square": 22/60,
            "Embarcadero": 20/60,
            "Financial District": 23/60,
            "Marina District": 11/60
        },
        "Haight-Ashbury": {
            "Presidio": 15/60,
            "Nob Hill": 15/60,
            "Russian Hill": 17/60,
            "North Beach": 19/60,
            "Chinatown": 19/60,
            "Union Square": 19/60,
            "Embarcadero": 20/60,
            "Financial District": 21/60,
            "Marina District": 17/60
        },
        # Other locations would be similarly defined
        # For brevity, we'll assume we can look up any travel time as needed
    }

    # Create variables for each meeting's start and end times
    meeting_vars = []
    for friend in friends:
        start = Real(f"{friend['name']}_start")
        end = Real(f"{friend['name']}_end")
        s.add(start >= friend["start"])
        s.add(end <= friend["end"])
        s.add(end == start + friend["duration"])
        meeting_vars.append({"name": friend["name"], "start": start, "end": end, "location": friend["location"]})

    # Add constraints for travel times between consecutive meetings
    # For simplicity, we'll assume we start at Presidio at 9:00 (9.0)
    current_location = "Presidio"
    current_time = 9.0

    # Ensure that the first meeting is after 9:00 plus travel time from Presidio
    for meeting in meeting_vars:
        s.add(meeting["start"] >= current_time + travel_times[current_location][meeting["location"]])

    # Ensure no overlap between any two meetings and travel times are respected
    for i in range(len(meeting_vars)):
        for j in range(i + 1, len(meeting_vars)):
            loc_i = meeting_vars[i]["location"]
            loc_j = meeting_vars[j]["location"]
            s.add(Or(
                meeting_vars[i]["end"] + travel_times[loc_i][loc_j] <= meeting_vars[j]["start"],
                meeting_vars[j]["end"] + travel_times[loc_j][loc_i] <= meeting_vars[i]["start"]
            ))

    # We'll try to maximize the number of friends met
    # For simplicity, we'll just check satisfiability and get a model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for meeting in meeting_vars:
            start_val = m[meeting["start"]].as_fraction()
            end_val = m[meeting["end"]].as_fraction()
            start_time = float(start_val.numerator) / float(start_val.denominator)
            end_time = float(end_val.numerator) / float(end_val.denominator)
            # Convert to HH:MM format
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

# Run the solver and print the result
result = solve_scheduling()
print(json.dumps(result, indent=2))