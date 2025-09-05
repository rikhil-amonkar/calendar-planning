import json
from z3 import Optimize, Int, Bool, If, And, Or, Implies, Sum, sat

def minutes_to_time(t):
    hour = t // 60
    minute = t % 60
    return f"{hour}:{minute:02d}"

def main():
    # Define meeting data for each friend.
    # Times here are in minutes from midnight.
    meetings_data = [
        {
            "person": "Mary",
            "location": "Golden Gate Park",
            "avail_start": 8 * 60 + 45,   # 8:45 => 525
            "avail_end": 11 * 60 + 45,    # 11:45 => 705
            "min_duration": 45
        },
        {
            "person": "Kevin",
            "location": "Haight-Ashbury",
            "avail_start": 10 * 60 + 15,  # 10:15 => 615
            "avail_end": 16 * 60 + 15,    # 16:15 => 975
            "min_duration": 90
        },
        {
            "person": "Deborah",
            "location": "Bayview",
            "avail_start": 15 * 60,       # 15:00 => 900
            "avail_end": 19 * 60 + 15,    # 19:15 => 1155
            "min_duration": 120
        },
        {
            "person": "Stephanie",
            "location": "Presidio",
            "avail_start": 10 * 60,       # 10:00 => 600
            "avail_end": 17 * 60 + 15,    # 17:15 => 1035
            "min_duration": 120
        },
        {
            "person": "Emily",
            "location": "Financial District",
            "avail_start": 11 * 60 + 30,  # 11:30 => 690
            "avail_end": 21 * 60 + 45,    # 21:45 => 1305
            "min_duration": 105
        }
    ]

    # Travel times in minutes between locations. 
    # Keys are (from, to) pairs.
    travel_times = {
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "Bayview"): 21,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Financial District"): 5,
        
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Bayview"): 23,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Financial District"): 26,
        
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Financial District"): 21,
        
        ("Bayview", "Embarcadero"): 19,
        ("Bayview", "Golden Gate Park"): 22,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "Presidio"): 31,
        ("Bayview", "Financial District"): 19,
        
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Bayview"): 31,
        ("Presidio", "Financial District"): 23,
        
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Bayview"): 19,
        ("Financial District", "Presidio"): 22,
    }

    # Starting point and arrival time
    start_location = "Embarcadero"
    arrival_time = 9 * 60  # 9:00 AM => 540 minutes

    # Create an Optimize instance.
    solver = Optimize()

    # Create decision variables for each meeting.
    meeting_vars = []
    for m in meetings_data:
        sch = Bool("sched_" + m["person"])
        start_var = Int("start_" + m["person"])
        end_var = Int("end_" + m["person"])
        meeting_vars.append({
            "person": m["person"],
            "location": m["location"],
            "avail_start": m["avail_start"],
            "avail_end": m["avail_end"],
            "min_duration": m["min_duration"],
            "scheduled": sch,
            "start": start_var,
            "end": end_var
        })
        # The meeting must start no earlier than the friend’s availability and the time it takes
        # to get there from the starting location.
        lower_bound = max(m["avail_start"], arrival_time + travel_times[(start_location, m["location"])])
        solver.add(Implies(sch, start_var >= lower_bound))
        solver.add(Implies(sch, start_var >= m["avail_start"]))
        solver.add(Implies(sch, end_var <= m["avail_end"]))
        solver.add(Implies(sch, end_var - start_var >= m["min_duration"]))
    
    # Add non-overlap constraints with travel times between any two scheduled meetings.
    n = len(meeting_vars)
    for i in range(n):
        for j in range(i + 1, n):
            m_i = meeting_vars[i]
            m_j = meeting_vars[j]
            travel_i_j = travel_times[(m_i["location"], m_j["location"])]
            travel_j_i = travel_times[(m_j["location"], m_i["location"])]
            # Either meeting i is scheduled before meeting j (including travel time)
            # or meeting j is scheduled before meeting i.
            no_overlap = Or(
                m_i["start"] >= m_j["end"] + travel_j_i,
                m_j["start"] >= m_i["end"] + travel_i_j
            )
            solver.add(Implies(And(m_i["scheduled"], m_j["scheduled"]), no_overlap))
    
    # Optionally, ensure times are non-negative.
    for m in meeting_vars:
        solver.add(Implies(m["scheduled"], m["start"] >= 0))
        solver.add(Implies(m["scheduled"], m["end"] >= 0))
    
    # Objective: maximize the number of meetings scheduled.
    total_meetings = Sum([If(m["scheduled"], 1, 0) for m in meeting_vars])
    solver.maximize(total_meetings)

    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        scheduled_meetings = []
        for mv in meeting_vars:
            if model.evaluate(mv["scheduled"]):
                start_val = model.evaluate(mv["start"]).as_long()
                end_val = model.evaluate(mv["end"]).as_long()
                scheduled_meetings.append({
                    "person": mv["person"],
                    "location": mv["location"],
                    "start": start_val,
                    "end": end_val
                })
        # Sort meetings by start time.
        scheduled_meetings.sort(key=lambda x: x["start"])
        for sm in scheduled_meetings:
            itinerary.append({
                "action": "meet",
                "location": sm["location"],
                "person": sm["person"],
                "start_time": minutes_to_time(sm["start"]),
                "end_time": minutes_to_time(sm["end"])
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        # If no schedule is found, output an empty itinerary.
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()