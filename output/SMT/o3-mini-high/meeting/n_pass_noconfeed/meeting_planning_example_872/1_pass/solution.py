import json
from z3 import *

def main():
    # Meeting data: availability times are in minutes from midnight.
    # 9:00 AM = 540, 21:00 = 1260, etc.
    meetings = [
        {"person": "Karen", "location": "Haight-Ashbury", "avail_start": 1260, "avail_end": 1305, "duration": 45},
        {"person": "Jessica", "location": "Nob Hill", "avail_start": 825,  "avail_end": 1260, "duration": 90},
        {"person": "Brian", "location": "Russian Hill", "avail_start": 930,  "avail_end": 1305, "duration": 60},
        {"person": "Kenneth", "location": "North Beach", "avail_start": 585,  "avail_end": 1260, "duration": 30},
        # Note: Jason is available 8:15 (495) to 11:45 (705), but you arrive at 9:00 (540)
        {"person": "Jason", "location": "Chinatown", "avail_start": 540, "avail_end": 705, "duration": 75},
        {"person": "Stephanie", "location": "Union Square", "avail_start": 885,  "avail_end": 1125, "duration": 105},
        {"person": "Kimberly", "location": "Embarcadero", "avail_start": 585, "avail_end": 1170, "duration": 75},
        {"person": "Steven", "location": "Financial District", "avail_start": 540, "avail_end": 1275, "duration": 60},
        {"person": "Mark", "location": "Marina District", "avail_start": 615, "avail_end": 780, "duration": 75}
    ]

    # Travel times (in minutes) between locations.
    travel_times = {
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Marina District"): 11,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "North Beach"): 19,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "Financial District"): 9,
        ("Nob Hill", "Marina District"): 11,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Union Square"): 10,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Marina District"): 7,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Haight-Ashbury"): 18,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Marina District"): 9,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Chinatown", "Nob Hill"): 9,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Embarcadero"): 5,
        ("Chinatown", "Financial District"): 5,
        ("Chinatown", "Marina District"): 12,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Russian Hill"): 13,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Embarcadero"): 11,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Marina District"): 18,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Chinatown"): 7,
        ("Embarcadero", "Union Square"): 10,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Marina District"): 12,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Nob Hill"): 8,
        ("Financial District", "Russian Hill"): 11,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Chinatown"): 5,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Marina District"): 15,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "Financial District"): 17
    }
    
    # Create an Optimize object.
    opt = Optimize()
    N = len(meetings)
    
    # For each meeting, create:
    #   s_vars[i]: start time (in minutes)
    #   sch_vars[i]: Boolean indicator if meeting 'i' is scheduled.
    #   order_vars[i]: order (position in the sequence) if scheduled; -1 if not scheduled.
    s_vars = [Int(f"s_{i}") for i in range(N)]
    sch_vars = [Bool(f"sch_{i}") for i in range(N)]
    order_vars = [Int(f"order_{i}") for i in range(N)]
    
    # Each meeting if scheduled must occur within its availability window.
    for i, m in enumerate(meetings):
        dur = m["duration"]
        opt.add(Implies(sch_vars[i], s_vars[i] >= m["avail_start"]))
        opt.add(Implies(sch_vars[i], s_vars[i] + dur <= m["avail_end"]))
        # Non-scheduled meetings get a dummy order (-1).
        opt.add(Implies(Not(sch_vars[i]), order_vars[i] == -1))
        # If scheduled, order must lie between 0 and N-1.
        opt.add(Implies(sch_vars[i], And(order_vars[i] >= 0, order_vars[i] < N)))
    
    # For every pair of different meetings, if both are scheduled then one must come before the other.
    # The travel time between locations is enforced between consecutive meetings.
    for i in range(N):
        for j in range(i+1, N):
            travel_ij = travel_times.get((meetings[i]["location"], meetings[j]["location"]))
            travel_ji = travel_times.get((meetings[j]["location"], meetings[i]["location"]))
            # If meeting i comes before meeting j then the end of i plus travel must be <= start of j.
            opt.add(Implies(And(sch_vars[i], sch_vars[j], order_vars[i] < order_vars[j]),
                        s_vars[i] + meetings[i]["duration"] + travel_ij <= s_vars[j]))
            # If meeting j comes before meeting i then the end of j plus travel must be <= start of i.
            opt.add(Implies(And(sch_vars[i], sch_vars[j], order_vars[j] < order_vars[i]),
                        s_vars[j] + meetings[j]["duration"] + travel_ji <= s_vars[i]))
            # If both meetings are scheduled, their order numbers must differ.
            opt.add(Implies(And(sch_vars[i], sch_vars[j]), order_vars[i] != order_vars[j]))
    
    # The first meeting (order 0) must be reachable from Presidio (arrival at 9:00, i.e., 540) plus travel time.
    for i in range(N):
        travel_from_presidio = travel_times.get(("Presidio", meetings[i]["location"]))
        opt.add(Implies(And(sch_vars[i], order_vars[i] == 0),
                        s_vars[i] >= 540 + travel_from_presidio))
    
    # If there is any scheduled meeting then at least one must have order 0.
    total_scheduled = Sum([If(sch_vars[i], 1, 0) for i in range(N)])
    opt.add(Or(total_scheduled == 0, Sum([If(And(sch_vars[i], order_vars[i] == 0), 1, 0) for i in range(N)]) >= 1))
    
    # Maximize the number of meetings scheduled.
    opt.maximize(total_scheduled)
    
    if opt.check() == sat:
        model = opt.model()
        scheduled_meetings = []
        for i in range(N):
            if is_true(model.evaluate(sch_vars[i])):
                order_val = model.evaluate(order_vars[i]).as_long()
                start_val = model.evaluate(s_vars[i]).as_long()
                scheduled_meetings.append((order_val, i, start_val))
        # Sort meetings by their scheduled order.
        scheduled_meetings.sort(key=lambda x: x[0])
        
        def format_time(t):
            hrs = t // 60
            mins = t % 60
            return f"{hrs}:{mins:02d}"
        
        itinerary = []
        for order_val, i, start_val in scheduled_meetings:
            m = meetings[i]
            itinerary.append({
                "action": "meet",
                "location": m["location"],
                "person": m["person"],
                "start_time": format_time(start_val),
                "end_time": format_time(start_val + m["duration"])
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()