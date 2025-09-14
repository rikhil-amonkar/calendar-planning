from z3 import *
import json

def minutes_to_time_str(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

def main():
    # Travel times between districts (in minutes)
    travel = {
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Nob Hill"): 27,
        ("Sunset District", "Pacific Heights"): 21,
        ("Sunset District", "Mission District"): 25,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "North Beach"): 28,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "Richmond District"): 12,
        ("Sunset District", "Embarcadero"): 30,
        ("Sunset District", "Alamo Square"): 17,

        ("Presidio", "Sunset District"): 15,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Mission District"): 26,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Alamo Square"): 19,

        ("Nob Hill", "Sunset District"): 24,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Mission District"): 13,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "Richmond District"): 14,
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "Alamo Square"): 11,

        ("Pacific Heights", "Sunset District"): 21,
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Mission District"): 15,
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "North Beach"): 9,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Pacific Heights", "Richmond District"): 12,
        ("Pacific Heights", "Embarcadero"): 10,
        ("Pacific Heights", "Alamo Square"): 10,

        ("Mission District", "Sunset District"): 24,
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Nob Hill"): 12,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "Marina District"): 19,
        ("Mission District", "North Beach"): 17,
        ("Mission District", "Russian Hill"): 15,
        ("Mission District", "Richmond District"): 20,
        ("Mission District", "Embarcadero"): 19,
        ("Mission District", "Alamo Square"): 11,

        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Mission District"): 20,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "Alamo Square"): 15,

        ("North Beach", "Sunset District"): 27,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Pacific Heights"): 8,
        ("North Beach", "Mission District"): 18,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Alamo Square"): 16,

        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Pacific Heights"): 7,
        ("Russian Hill", "Mission District"): 16,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "Alamo Square"): 15,

        ("Richmond District", "Sunset District"): 11,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Mission District"): 20,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Alamo Square"): 13,

        ("Embarcadero", "Sunset District"): 30,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Pacific Heights"): 11,
        ("Embarcadero", "Mission District"): 20,
        ("Embarcadero", "Marina District"): 12,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Alamo Square"): 19,

        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "Pacific Heights"): 10,
        ("Alamo Square", "Mission District"): 10,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "Richmond District"): 11,
        ("Alamo Square", "Embarcadero"): 16,
    }

    # Meeting constraints and details for each friend
    # Times are represented in minutes from midnight.
    meetings = [
        {"name": "Charles", "location": "Presidio", "avail_start": 13*60+15, "avail_end": 15*60, "min_duration": 105},
        {"name": "Robert", "location": "Nob Hill", "avail_start": 13*60+15, "avail_end": 17*60+30, "min_duration": 90},
        {"name": "Nancy", "location": "Pacific Heights", "avail_start": 14*60+45, "avail_end": 22*60, "min_duration": 105},
        {"name": "Brian", "location": "Mission District", "avail_start": 15*60+30, "avail_end": 22*60, "min_duration": 60},
        {"name": "Kimberly", "location": "Marina District", "avail_start": 17*60, "avail_end": 19*60+45, "min_duration": 75},
        {"name": "David", "location": "North Beach", "avail_start": 14*60+45, "avail_end": 16*60+30, "min_duration": 75},
        {"name": "William", "location": "Russian Hill", "avail_start": 12*60+30, "avail_end": 19*60+15, "min_duration": 120},
        {"name": "Jeffrey", "location": "Richmond District", "avail_start": 12*60, "avail_end": 19*60+15, "min_duration": 45},
        {"name": "Karen", "location": "Embarcadero", "avail_start": 14*60+15, "avail_end": 20*60+45, "min_duration": 60},
        {"name": "Joshua", "location": "Alamo Square", "avail_start": 18*60+45, "avail_end": 22*60, "min_duration": 60},
    ]

    N = len(meetings)
    opt = Optimize()

    # Create SMT variables for each meeting:
    # - meet_vars[i]: Boolean indicating if we schedule the meeting with friend i.
    # - start_vars[i]: The start time (in minutes) of the meeting.
    # - pos_vars[i]: The position (order) of the meeting in our itinerary (0 if not scheduled).
    meet_vars = []
    start_vars = []
    pos_vars = []
    for i in range(N):
        m = Bool(f"meet_{i}")
        s = Int(f"start_{i}")
        p = Int(f"pos_{i}")
        meet_vars.append(m)
        start_vars.append(s)
        pos_vars.append(p)
        # If meeting is scheduled then position is between 1 and N; otherwise it is 0.
        opt.add(Implies(m, And(p >= 1, p <= N)))
        opt.add(Implies(Not(m), p == 0))
        # Start time must be within a plausible day.
        opt.add(s >= 0, s <= 1440)
        # If scheduled, meeting must occur within the friend's available window.
        avail_start = meetings[i]["avail_start"]
        avail_end = meetings[i]["avail_end"]
        min_dur = meetings[i]["min_duration"]
        opt.add(Implies(m, s >= avail_start))
        opt.add(Implies(m, s + min_dur <= avail_end))

    # Ensure that if any meeting is scheduled, exactly one of them is the first meeting (position 1).
    total_meetings = Sum([If(m, 1, 0) for m in meet_vars])
    first_count = Sum([If(And(meet_vars[i], pos_vars[i] == 1), 1, 0) for i in range(N)])
    opt.add(Implies(total_meetings > 0, first_count == 1))

    # For any meeting that is first in sequence, account for travel time from the starting point.
    # You arrive at "Sunset District" at 9:00 (540 minutes).
    for i in range(N):
        loc = meetings[i]["location"]
        travel_time = travel[("Sunset District", loc)]
        opt.add(Implies(And(meet_vars[i], pos_vars[i] == 1), start_vars[i] >= 540 + travel_time))

    # For every pair of scheduled meetings, enforce ordering:
    # If meeting i comes before meeting j, then the start time of j must be at least
    # the end time of i (start time + minimum duration) plus the travel time from i's location to j's location.
    for i in range(N):
        for j in range(N):
            if i != j:
                travel_time_ij = travel[(meetings[i]["location"], meetings[j]["location"])]
                dur_i = meetings[i]["min_duration"]
                opt.add(Implies(And(meet_vars[i], meet_vars[j], pos_vars[i] < pos_vars[j]),
                                start_vars[j] >= start_vars[i] + dur_i + travel_time_ij))
                # Also, if both meetings are scheduled, their positions must be distinct.
                opt.add(Implies(And(meet_vars[i], meet_vars[j]), pos_vars[i] != pos_vars[j]))

    # Objective: maximize the total number of meetings scheduled.
    opt.maximize(total_meetings)

    # Check for a solution and build the itinerary.
    if opt.check() == sat:
        model = opt.model()
        schedule = []
        for i in range(N):
            if is_true(model.evaluate(meet_vars[i])):
                s_time = model.evaluate(start_vars[i]).as_long()
                dur = meetings[i]["min_duration"]
                position = model.evaluate(pos_vars[i]).as_long()
                schedule.append((position, meetings[i]["name"], meetings[i]["location"], s_time, s_time + dur))
        # Sort scheduled meetings by their position.
        schedule.sort(key=lambda x: x[0])
        itinerary = []
        for pos, name, location, start_time, end_time in schedule:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": minutes_to_time_str(start_time),
                "end_time": minutes_to_time_str(end_time)
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()