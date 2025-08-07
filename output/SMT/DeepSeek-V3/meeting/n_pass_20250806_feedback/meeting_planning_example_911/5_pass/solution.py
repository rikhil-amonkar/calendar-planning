from z3 import *
import json

def solve_scheduling():
    s = Optimize()

    # Friends data
    friends = {
        "Nancy": {"location": "Nob Hill", "start": "08:15", "end": "12:45", "duration": 90},
        "Stephanie": {"location": "Haight-Ashbury", "start": "10:15", "end": "12:15", "duration": 75},
        "David": {"location": "Marina District", "start": "11:15", "end": "13:15", "duration": 120},
        "Elizabeth": {"location": "Union Square", "start": "11:30", "end": "21:00", "duration": 60},
        "Robert": {"location": "Financial District", "start": "13:15", "end": "15:15", "duration": 45},
        "Brian": {"location": "Embarcadero", "start": "14:15", "end": "16:00", "duration": 105},
        "Melissa": {"location": "Richmond District", "start": "14:00", "end": "19:30", "duration": 30},
        "James": {"location": "Presidio", "start": "15:00", "end": "18:15", "duration": 120},
        "Sarah": {"location": "Golden Gate Park", "start": "17:00", "end": "19:15", "duration": 75},
        "Steven": {"location": "North Beach", "start": "17:30", "end": "20:30", "duration": 15}
    }

    # Travel times matrix (minutes)
    travel_times = {
        "The Castro": {"Nob Hill": 16, "Haight-Ashbury": 6, "Marina District": 21, "Union Square": 19, 
                      "Financial District": 21, "Embarcadero": 22, "Richmond District": 16, 
                      "Presidio": 20, "Golden Gate Park": 11, "North Beach": 20},
        "Nob Hill": {"The Castro": 16, "Haight-Ashbury": 13, "Marina District": 11, "Union Square": 7,
                    "Financial District": 9, "Embarcadero": 9, "Richmond District": 14,
                    "Presidio": 17, "Golden Gate Park": 17, "North Beach": 8},
        "Haight-Ashbury": {"The Castro": 6, "Nob Hill": 13, "Marina District": 17, "Union Square": 19,
                          "Financial District": 21, "Embarcadero": 20, "Richmond District": 10,
                          "Presidio": 15, "Golden Gate Park": 7, "North Beach": 19},
        # ... (other travel times would be added here)
    }

    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Create variables
    meeting_vars = {}
    for name in friends:
        meeting_vars[name] = {
            "start": Int(f"start_{name}"),
            "end": Int(f"end_{name}"),
            "met": Bool(f"met_{name}")
        }
        s.add(meeting_vars[name]["end"] == meeting_vars[name]["start"] + friends[name]["duration"])
        s.add(Implies(meeting_vars[name]["met"],
                     And(meeting_vars[name]["start"] >= time_to_minutes(friends[name]["start"]),
                         meeting_vars[name]["end"] <= time_to_minutes(friends[name]["end"]))))

    # Initial constraints
    current_location = "The Castro"
    current_time = 540  # 9:00 AM

    # First meeting must be Nancy at Nob Hill
    s.add(meeting_vars["Nancy"]["met"])
    s.add(meeting_vars["Nancy"]["start"] >= current_time + travel_times[current_location]["Nob Hill"])

    # Create sequence variables to model ordering
    sequence = [name for name in friends]
    prev_location = "Nob Hill"
    prev_end = meeting_vars["Nancy"]["end"]

    # Add travel time constraints between consecutive meetings
    for i in range(1, len(sequence)):
        curr_name = sequence[i]
        curr_location = friends[curr_name]["location"]
        s.add(Implies(And(meeting_vars[sequence[i-1]]["met"], meeting_vars[curr_name]["met"]),
                     meeting_vars[curr_name]["start"] >= meeting_vars[sequence[i-1]]["end"] + 
                     travel_times[friends[sequence[i-1]]["location"]][curr_location]))

    # Maximize number of meetings
    s.maximize(Sum([If(meeting_vars[name]["met"], 1, 0) for name in friends]))

    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in friends:
            if is_true(model[meeting_vars[name]["met"]]):
                start = model[meeting_vars[name]["start"]].as_long()
                end = model[meeting_vars[name]["end"]].as_long()
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": minutes_to_time(start),
                    "end_time": minutes_to_time(end)
                })
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid schedule found"}

solution = solve_scheduling()
print(json.dumps(solution, indent=2))