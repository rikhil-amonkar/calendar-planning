from z3 import *
import json

def solve_scheduling_problem():
    # Initialize solver
    s = Solver()

    # Locations and their indices
    locations = {
        "Haight-Ashbury": 0,
        "Mission District": 1,
        "Bayview": 2,
        "Pacific Heights": 3,
        "Russian Hill": 4,
        "Fisherman's Wharf": 5
    }

    # Travel times matrix (minutes)
    travel_times = [
        [0, 11, 18, 12, 17, 23],
        [11, 0, 15, 16, 15, 22],
        [18, 15, 0, 23, 23, 25],
        [12, 16, 23, 0, 7, 13],
        [17, 15, 23, 7, 0, 7],
        [23, 22, 25, 13, 7, 0]
    ]

    # Friends data: name, location, available start, available end, min duration
    friends = [
        ("Stephanie", 1, 8*60+15, 13*60+45, 90),
        ("Sandra", 2, 13*60+0, 19*60+30, 15),
        ("Richard", 3, 7*60+15, 10*60+15, 75),
        ("Brian", 4, 12*60+15, 16*60+0, 120),
        ("Jason", 5, 8*60+30, 17*60+45, 60)
    ]

    # Create meeting variables
    meets = []
    for name, loc, avail_start, avail_end, min_dur in friends:
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        s.add(start >= avail_start)
        s.add(end <= avail_end)
        s.add(end == start + min_dur)
        meets.append((name, loc, start, end))

    # Starting point
    current_time = 540  # 9:00 AM in minutes
    current_loc = 0  # Haight-Ashbury

    # Create sequence variables
    sequence = [Int(f'seq_{i}') for i in range(len(friends))]
    s.add(Distinct(sequence))
    for seq in sequence:
        s.add(seq >= 0, seq < len(friends))

    # Travel time constraints between consecutive meetings
    for i in range(len(friends)):
        for j in range(len(friends)):
            if i != j:
                name_i, loc_i, start_i, end_i = meets[i]
                name_j, loc_j, start_j, end_j = meets[j]
                s.add(Implies(sequence[i] < sequence[j],
                            start_j >= end_i + travel_times[loc_i][loc_j]))

    # First meeting must be reachable from starting location
    for i in range(len(friends)):
        name, loc, start, end = meets[i]
        s.add(Implies(sequence[i] == 0,
                     start >= current_time + travel_times[current_loc][loc]))

    # Richard must be first (only available until 10:15)
    for i, (name, _, _, _) in enumerate(meets):
        if name == "Richard":
            s.add(sequence[i] == 0)

    # Solve the problem
    if s.check() == sat:
        m = s.model()
        # Get ordered meetings
        ordered = sorted([(i, m.evaluate(sequence[i]).as_long())
                        for i in range(len(friends))], key=lambda x: x[1])
        itinerary = []
        for i, pos in ordered:
            name, loc, start, end = meets[i]
            start_val = m.evaluate(start).as_long()
            end_val = m.evaluate(end).as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": f"{start_val//60:02d}:{start_val%60:02d}",
                "end_time": f"{end_val//60:02d}:{end_val%60:02d}"
            })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))