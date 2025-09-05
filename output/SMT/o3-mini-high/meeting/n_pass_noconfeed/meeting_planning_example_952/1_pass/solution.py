import json
from z3 import *

def main():
    # Friend data: names, locations, availability windows (in minutes from midnight), and minimum meeting durations.
    friend_names = [
        "Brian", "Richard", "Ashley", "Elizabeth", "Jessica",
        "Deborah", "Kimberly", "Matthew", "Kenneth", "Anthony"
    ]
    friend_locations = [
        "North Beach", "Fisherman's Wharf", "Haight-Ashbury", "Nob Hill", "Golden Gate Park",
        "Union Square", "Alamo Square", "Presidio", "Chinatown", "Pacific Heights"
    ]
    # Availability times: convert e.g., 13:00 -> 780, etc.
    avail_start = [780, 660, 900, 705, 1200, 1050, 1050, 495, 825, 855]
    avail_end   = [1140,765,1230,1110,1305,1320,1275,540,1170,960]
    min_duration = [90, 60, 90, 75, 105, 60, 45, 15, 105, 30]

    # Travel times dictionary for all locations. Keys are (from, to) pairs.
    travel = {}
    # From Bayview to other locations
    travel[("Bayview", "North Beach")] = 22
    travel[("Bayview", "Fisherman's Wharf")] = 25
    travel[("Bayview", "Haight-Ashbury")] = 19
    travel[("Bayview", "Nob Hill")] = 20
    travel[("Bayview", "Golden Gate Park")] = 22
    travel[("Bayview", "Union Square")] = 18
    travel[("Bayview", "Alamo Square")] = 16
    travel[("Bayview", "Presidio")] = 32
    travel[("Bayview", "Chinatown")] = 19
    travel[("Bayview", "Pacific Heights")] = 23

    # From North Beach
    travel[("North Beach", "Bayview")] = 25
    travel[("North Beach", "Fisherman's Wharf")] = 5
    travel[("North Beach", "Haight-Ashbury")] = 18
    travel[("North Beach", "Nob Hill")] = 7
    travel[("North Beach", "Golden Gate Park")] = 22
    travel[("North Beach", "Union Square")] = 7
    travel[("North Beach", "Alamo Square")] = 16
    travel[("North Beach", "Presidio")] = 17
    travel[("North Beach", "Chinatown")] = 6
    travel[("North Beach", "Pacific Heights")] = 8

    # From Fisherman's Wharf
    travel[("Fisherman's Wharf", "Bayview")] = 26
    travel[("Fisherman's Wharf", "North Beach")] = 6
    travel[("Fisherman's Wharf", "Haight-Ashbury")] = 22
    travel[("Fisherman's Wharf", "Nob Hill")] = 11
    travel[("Fisherman's Wharf", "Golden Gate Park")] = 25
    travel[("Fisherman's Wharf", "Union Square")] = 13
    travel[("Fisherman's Wharf", "Alamo Square")] = 21
    travel[("Fisherman's Wharf", "Presidio")] = 17
    travel[("Fisherman's Wharf", "Chinatown")] = 12
    travel[("Fisherman's Wharf", "Pacific Heights")] = 12

    # From Haight-Ashbury
    travel[("Haight-Ashbury", "Bayview")] = 18
    travel[("Haight-Ashbury", "North Beach")] = 19
    travel[("Haight-Ashbury", "Fisherman's Wharf")] = 23
    travel[("Haight-Ashbury", "Nob Hill")] = 15
    travel[("Haight-Ashbury", "Golden Gate Park")] = 7
    travel[("Haight-Ashbury", "Union Square")] = 19
    travel[("Haight-Ashbury", "Alamo Square")] = 5
    travel[("Haight-Ashbury", "Presidio")] = 15
    travel[("Haight-Ashbury", "Chinatown")] = 19
    travel[("Haight-Ashbury", "Pacific Heights")] = 12

    # From Nob Hill
    travel[("Nob Hill", "Bayview")] = 19
    travel[("Nob Hill", "North Beach")] = 8
    travel[("Nob Hill", "Fisherman's Wharf")] = 10
    travel[("Nob Hill", "Haight-Ashbury")] = 13
    travel[("Nob Hill", "Golden Gate Park")] = 17
    travel[("Nob Hill", "Union Square")] = 7
    travel[("Nob Hill", "Alamo Square")] = 11
    travel[("Nob Hill", "Presidio")] = 17
    travel[("Nob Hill", "Chinatown")] = 6
    travel[("Nob Hill", "Pacific Heights")] = 8

    # From Golden Gate Park
    travel[("Golden Gate Park", "Bayview")] = 23
    travel[("Golden Gate Park", "North Beach")] = 23
    travel[("Golden Gate Park", "Fisherman's Wharf")] = 24
    travel[("Golden Gate Park", "Haight-Ashbury")] = 7
    travel[("Golden Gate Park", "Nob Hill")] = 20
    travel[("Golden Gate Park", "Union Square")] = 22
    travel[("Golden Gate Park", "Alamo Square")] = 9
    travel[("Golden Gate Park", "Presidio")] = 11
    travel[("Golden Gate Park", "Chinatown")] = 23
    travel[("Golden Gate Park", "Pacific Heights")] = 16

    # From Union Square
    travel[("Union Square", "Bayview")] = 15
    travel[("Union Square", "North Beach")] = 10
    travel[("Union Square", "Fisherman's Wharf")] = 15
    travel[("Union Square", "Haight-Ashbury")] = 18
    travel[("Union Square", "Nob Hill")] = 9
    travel[("Union Square", "Golden Gate Park")] = 22
    travel[("Union Square", "Alamo Square")] = 15
    travel[("Union Square", "Presidio")] = 24
    travel[("Union Square", "Chinatown")] = 7
    travel[("Union Square", "Pacific Heights")] = 15

    # From Alamo Square
    travel[("Alamo Square", "Bayview")] = 16
    travel[("Alamo Square", "North Beach")] = 15
    travel[("Alamo Square", "Fisherman's Wharf")] = 19
    travel[("Alamo Square", "Haight-Ashbury")] = 5
    travel[("Alamo Square", "Nob Hill")] = 11
    travel[("Alamo Square", "Golden Gate Park")] = 9
    travel[("Alamo Square", "Union Square")] = 14
    travel[("Alamo Square", "Presidio")] = 17
    travel[("Alamo Square", "Chinatown")] = 15
    travel[("Alamo Square", "Pacific Heights")] = 10

    # From Presidio
    travel[("Presidio", "Bayview")] = 31
    travel[("Presidio", "North Beach")] = 18
    travel[("Presidio", "Fisherman's Wharf")] = 19
    travel[("Presidio", "Haight-Ashbury")] = 15
    travel[("Presidio", "Nob Hill")] = 18
    travel[("Presidio", "Golden Gate Park")] = 12
    travel[("Presidio", "Union Square")] = 22
    travel[("Presidio", "Alamo Square")] = 19
    travel[("Presidio", "Chinatown")] = 21
    travel[("Presidio", "Pacific Heights")] = 11

    # From Chinatown
    travel[("Chinatown", "Bayview")] = 20
    travel[("Chinatown", "North Beach")] = 3
    travel[("Chinatown", "Fisherman's Wharf")] = 8
    travel[("Chinatown", "Haight-Ashbury")] = 19
    travel[("Chinatown", "Nob Hill")] = 9
    travel[("Chinatown", "Golden Gate Park")] = 23
    travel[("Chinatown", "Union Square")] = 7
    travel[("Chinatown", "Alamo Square")] = 17
    travel[("Chinatown", "Presidio")] = 19
    travel[("Chinatown", "Pacific Heights")] = 10

    # From Pacific Heights
    travel[("Pacific Heights", "Bayview")] = 22
    travel[("Pacific Heights", "North Beach")] = 9
    travel[("Pacific Heights", "Fisherman's Wharf")] = 13
    travel[("Pacific Heights", "Haight-Ashbury")] = 11
    travel[("Pacific Heights", "Nob Hill")] = 8
    travel[("Pacific Heights", "Golden Gate Park")] = 15
    travel[("Pacific Heights", "Union Square")] = 12
    travel[("Pacific Heights", "Alamo Square")] = 10
    travel[("Pacific Heights", "Presidio")] = 11
    travel[("Pacific Heights", "Chinatown")] = 11

    # Create the Z3 optimizer instance.
    opt = Optimize()

    # We define a schedule with a fixed number of slots.
    # Each slot is assigned a meeting represented by an integer:
    # 0-9 correspond to friend meetings; 10 indicates an empty slot.
    max_slots = 10
    meeting_vars = [Int(f"meet_{i}") for i in range(max_slots)]
    start_vars = [Int(f"start_{i}") for i in range(max_slots)]
    end_vars = [Int(f"end_{i}") for i in range(max_slots)]

    for i in range(max_slots):
        # Meeting id must be between 0 and 10 (10 means no meeting scheduled in that slot)
        opt.add(meeting_vars[i] >= 0, meeting_vars[i] <= 10)
        # If a slot is empty, set its start and end times to 0.
        opt.add(If(meeting_vars[i] == 10, And(start_vars[i] == 0, end_vars[i] == 0), True))
        # For each friend assignment (0-9), enforce availability and minimum meeting duration.
        for j in range(10):
            opt.add(Implies(
                meeting_vars[i] == j,
                And(
                    start_vars[i] >= avail_start[j],
                    end_vars[i] <= avail_end[j],
                    end_vars[i] - start_vars[i] >= min_duration[j]
                )
            ))

    # Contiguity: once an empty slot is reached, all later slots must be empty.
    for i in range(max_slots - 1):
        opt.add(Implies(meeting_vars[i] == 10, meeting_vars[i+1] == 10))

    # Distinct meetings: no friend is met twice.
    for i in range(max_slots):
        for k in range(i+1, max_slots):
            opt.add(Implies(And(meeting_vars[i] != 10, meeting_vars[k] != 10),
                            meeting_vars[i] != meeting_vars[k]))

    # Travel constraints.
    # You start at Bayview at 9:00 AM (540 minutes).
    # For the first scheduled meeting, the meeting start time must be at least the arrival time at that location.
    opt.add(Implies(
        meeting_vars[0] != 10,
        start_vars[0] >= 540 + Sum([If(meeting_vars[0] == j, travel[("Bayview", friend_locations[j])], 0) for j in range(10)])
    ))

    # For subsequent scheduled meetings, ensure there is enough travel time from the previous meeting.
    for i in range(1, max_slots):
        travel_expr = Sum([
            If(And(meeting_vars[i-1] == j, meeting_vars[i] == k),
               travel[(friend_locations[j], friend_locations[k])],
               0)
            for j in range(10) for k in range(10)
        ])
        opt.add(Implies(
            meeting_vars[i] != 10,
            start_vars[i] >= end_vars[i-1] + travel_expr
        ))

    # Objective: maximize the number of meetings scheduled.
    total_meetings = Sum([If(meeting_vars[i] != 10, 1, 0) for i in range(max_slots)])
    opt.maximize(total_meetings)

    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        # Function to convert minutes-from-midnight into H:MM format string.
        def format_time(t):
            h = t // 60
            m_ = t % 60
            return f"{h}:{m_:02d}"
        # Build the itinerary from the scheduled meeting slots.
        for i in range(max_slots):
            m_val = model.evaluate(meeting_vars[i]).as_long()
            if m_val == 10:
                break
            s_time = model.evaluate(start_vars[i]).as_long()
            e_time = model.evaluate(end_vars[i]).as_long()
            itinerary.append({
                "action": "meet",
                "location": friend_locations[m_val],
                "person": friend_names[m_val],
                "start_time": format_time(s_time),
                "end_time": format_time(e_time)
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()