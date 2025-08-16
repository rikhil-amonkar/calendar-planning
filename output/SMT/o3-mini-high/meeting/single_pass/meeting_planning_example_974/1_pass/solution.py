from z3 import Optimize, Int, Bool, And, Or, If, Implies, sat
import json

# Helper: convert minutes (offset from 9:00AM) into HH:MM 24-hour format.
def minutes_to_time(mins):
    total = mins + 9 * 60  # because time 0 corresponds to 9:00
    hh = total // 60
    mm = total % 60
    return f"{hh:02d}:{mm:02d}"

def main():
    # --- Data definition ---
    # Each friend record contains:
    #   person = friend name
    #   location = friend’s district (where the meeting takes place)
    #   avail_start, avail_end = friend’s available time window in minutes (offset from 9:00)
    #   dur = required meeting duration in minutes
    friends = [
        {"person": "Charles", "location": "Presidio",         "avail_start": 255, "avail_end": 360, "dur": 105},
        {"person": "Robert",  "location": "Nob Hill",         "avail_start": 255, "avail_end": 510, "dur": 90},
        {"person": "Nancy",   "location": "Pacific Heights",  "avail_start": 345, "avail_end": 780, "dur": 105},
        {"person": "Brian",   "location": "Mission District", "avail_start": 390, "avail_end": 780, "dur": 60},
        {"person": "Kimberly","location": "Marina District",  "avail_start": 480, "avail_end": 645, "dur": 75},
        {"person": "David",   "location": "North Beach",      "avail_start": 345, "avail_end": 450, "dur": 75},
        {"person": "William", "location": "Russian Hill",     "avail_start": 210, "avail_end": 615, "dur": 120},
        {"person": "Jeffrey", "location": "Richmond District","avail_start": 180, "avail_end": 615, "dur": 45},
        {"person": "Karen",   "location": "Embarcadero",      "avail_start": 315, "avail_end": 705, "dur": 60},
        {"person": "Joshua",  "location": "Alamo Square",     "avail_start": 585, "avail_end": 780, "dur": 60}
    ]
    # The travel times (in minutes) between districts.
    # Key: (origin, destination)
    travel_data = [
        ("Sunset District", "Presidio", 16),
        ("Sunset District", "Nob Hill", 27),
        ("Sunset District", "Pacific Heights", 21),
        ("Sunset District", "Mission District", 25),
        ("Sunset District", "Marina District", 21),
        ("Sunset District", "North Beach", 28),
        ("Sunset District", "Russian Hill", 24),
        ("Sunset District", "Richmond District", 12),
        ("Sunset District", "Embarcadero", 30),
        ("Sunset District", "Alamo Square", 17),
        ("Presidio", "Sunset District", 15),
        ("Presidio", "Nob Hill", 18),
        ("Presidio", "Pacific Heights", 11),
        ("Presidio", "Mission District", 26),
        ("Presidio", "Marina District", 11),
        ("Presidio", "North Beach", 18),
        ("Presidio", "Russian Hill", 14),
        ("Presidio", "Richmond District", 7),
        ("Presidio", "Embarcadero", 20),
        ("Presidio", "Alamo Square", 19),
        ("Nob Hill", "Sunset District", 24),
        ("Nob Hill", "Presidio", 17),
        ("Nob Hill", "Pacific Heights", 8),
        ("Nob Hill", "Mission District", 13),
        ("Nob Hill", "Marina District", 11),
        ("Nob Hill", "North Beach", 8),
        ("Nob Hill", "Russian Hill", 5),
        ("Nob Hill", "Richmond District", 14),
        ("Nob Hill", "Embarcadero", 9),
        ("Nob Hill", "Alamo Square", 11),
        ("Pacific Heights", "Sunset District", 21),
        ("Pacific Heights", "Presidio", 11),
        ("Pacific Heights", "Nob Hill", 8),
        ("Pacific Heights", "Mission District", 15),
        ("Pacific Heights", "Marina District", 6),
        ("Pacific Heights", "North Beach", 9),
        ("Pacific Heights", "Russian Hill", 7),
        ("Pacific Heights", "Richmond District", 12),
        ("Pacific Heights", "Embarcadero", 10),
        ("Pacific Heights", "Alamo Square", 10),
        ("Mission District", "Sunset District", 24),
        ("Mission District", "Presidio", 25),
        ("Mission District", "Nob Hill", 12),
        ("Mission District", "Pacific Heights", 16),
        ("Mission District", "Marina District", 19),
        ("Mission District", "North Beach", 17),
        ("Mission District", "Russian Hill", 15),
        ("Mission District", "Richmond District", 20),
        ("Mission District", "Embarcadero", 19),
        ("Mission District", "Alamo Square", 11),
        ("Marina District", "Sunset District", 19),
        ("Marina District", "Presidio", 10),
        ("Marina District", "Nob Hill", 12),
        ("Marina District", "Pacific Heights", 7),
        ("Marina District", "Mission District", 20),
        ("Marina District", "North Beach", 11),
        ("Marina District", "Russian Hill", 8),
        ("Marina District", "Richmond District", 11),
        ("Marina District", "Embarcadero", 14),
        ("Marina District", "Alamo Square", 15),
        ("North Beach", "Sunset District", 27),
        ("North Beach", "Presidio", 17),
        ("North Beach", "Nob Hill", 7),
        ("North Beach", "Pacific Heights", 8),
        ("North Beach", "Mission District", 18),
        ("North Beach", "Marina District", 9),
        ("North Beach", "Russian Hill", 4),
        ("North Beach", "Richmond District", 18),
        ("North Beach", "Embarcadero", 6),
        ("North Beach", "Alamo Square", 16),
        ("Russian Hill", "Sunset District", 23),
        ("Russian Hill", "Presidio", 14),
        ("Russian Hill", "Nob Hill", 5),
        ("Russian Hill", "Pacific Heights", 7),
        ("Russian Hill", "Mission District", 16),
        ("Russian Hill", "Marina District", 7),
        ("Russian Hill", "North Beach", 5),
        ("Russian Hill", "Richmond District", 14),
        ("Russian Hill", "Embarcadero", 8),
        ("Russian Hill", "Alamo Square", 15),
        ("Richmond District", "Sunset District", 11),
        ("Richmond District", "Presidio", 7),
        ("Richmond District", "Nob Hill", 17),
        ("Richmond District", "Pacific Heights", 10),
        ("Richmond District", "Mission District", 20),
        ("Richmond District", "Marina District", 9),
        ("Richmond District", "North Beach", 17),
        ("Richmond District", "Russian Hill", 13),
        ("Richmond District", "Embarcadero", 19),
        ("Richmond District", "Alamo Square", 13),
        ("Embarcadero", "Sunset District", 30),
        ("Embarcadero", "Presidio", 20),
        ("Embarcadero", "Nob Hill", 10),
        ("Embarcadero", "Pacific Heights", 11),
        ("Embarcadero", "Mission District", 20),
        ("Embarcadero", "Marina District", 12),
        ("Embarcadero", "North Beach", 5),
        ("Embarcadero", "Russian Hill", 8),
        ("Embarcadero", "Richmond District", 21),
        ("Embarcadero", "Alamo Square", 19),
        ("Alamo Square", "Sunset District", 16),
        ("Alamo Square", "Presidio", 17),
        ("Alamo Square", "Nob Hill", 11),
        ("Alamo Square", "Pacific Heights", 10),
        ("Alamo Square", "Mission District", 10),
        ("Alamo Square", "Marina District", 15),
        ("Alamo Square", "North Beach", 15),
        ("Alamo Square", "Russian Hill", 13),
        ("Alamo Square", "Richmond District", 11),
        ("Alamo Square", "Embarcadero", 16),
    ]
    travel = {}
    for frm, to, time in travel_data:
        travel[(frm, to)] = time

    # --- Z3 model definition ---
    opt = Optimize()
    n = len(friends)
    # For each friend, a Boolean to decide if we schedule a meeting,
    # and an integer meeting start time (measured in minutes after 9:00AM).
    scheduled = [Bool(f"scheduled_{i}") for i in range(n)]
    t_vars    = [Int(f"t_{i}") for i in range(n)]
    
    # Every meeting start time is nonnegative.
    for i in range(n):
        opt.add(t_vars[i] >= 0)
    
    # For each friend meeting, add time-window constraints (if the meeting is scheduled)
    for i, f in enumerate(friends):
        # Must start no earlier than friend availability.
        opt.add(Implies(scheduled[i], t_vars[i] >= f["avail_start"]))
        # Must finish (start + meeting duration) by the friend’s available end.
        opt.add(Implies(scheduled[i], t_vars[i] <= f["avail_end"] - f["dur"]))
        # Additionally, if we go directly from Sunset District (where we are at 9:00),
        # we cannot arrive before the travel time from "Sunset District" to the friend’s location.
        if ("Sunset District", f["location"]) in travel:
            direct_travel = travel[("Sunset District", f["location"])]
            opt.add(Implies(scheduled[i], t_vars[i] >= direct_travel))
        else:
            opt.add(Implies(scheduled[i], t_vars[i] >= 0))
    
    # Add disjunctive (non-overlap) constraints with travel time between any two scheduled meetings.
    # If both meeting i and meeting j are scheduled, then either i is scheduled before j (with travel from i to j)
    # or vice-versa.
    for i in range(n):
        for j in range(i+1, n):
            loc_i = friends[i]["location"]
            loc_j = friends[j]["location"]
            travel_ij = travel.get((loc_i, loc_j), 0)
            travel_ji = travel.get((loc_j, loc_i), 0)
            opt.add(Implies(And(scheduled[i], scheduled[j]),
                Or( t_vars[i] + friends[i]["dur"] + travel_ij <= t_vars[j],
                    t_vars[j] + friends[j]["dur"] + travel_ji <= t_vars[i]
                )))
    
    # Objective: maximize the number of meetings scheduled.
    objective = Sum([If(scheduled[i], 1, 0) for i in range(n)])
    opt.maximize(objective)
    
    # Solve the optimization problem.
    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        # Collect scheduled meetings with their start times; meeting end time is start + required duration.
        scheduled_meetings = []
        for i, f in enumerate(friends):
            if m.evaluate(scheduled[i]):
                start_val = m.evaluate(t_vars[i]).as_long()
                end_val   = start_val + f["dur"]
                scheduled_meetings.append((start_val, {
                    "action": "meet",
                    "person": f["person"],
                    "start_time": minutes_to_time(start_val),
                    "end_time": minutes_to_time(end_val)
                }))
        # Order the meetings by their start times.
        scheduled_meetings.sort(key=lambda x: x[0])
        for _, meeting in scheduled_meetings:
            itinerary.append(meeting)
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(result, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()