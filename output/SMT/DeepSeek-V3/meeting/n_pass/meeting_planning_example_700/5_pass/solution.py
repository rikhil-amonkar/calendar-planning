from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Friends data: name, location, available start (minutes from midnight), available end, min duration
    friends = [
        ("Kevin", "Pacific Heights", 7*60 + 15, 8*60 + 45, 90),
        ("Michelle", "Golden Gate Park", 20*60 + 0, 21*60 + 0, 15),
        ("Emily", "Fisherman's Wharf", 16*60 + 15, 19*60 + 0, 30),
        ("Mark", "Marina District", 18*60 + 15, 19*60 + 45, 75),
        ("Barbara", "Alamo Square", 17*60 + 0, 19*60 + 0, 120),
        ("Laura", "Sunset District", 19*60 + 0, 21*60 + 15, 75),
        ("Mary", "Nob Hill", 17*60 + 30, 19*60 + 0, 45),
        ("Helen", "North Beach", 11*60 + 0, 12*60 + 15, 45)
    ]

    # Create variables for each friend's meeting
    start_vars = [Int(f'start_{name}') for name, _, _, _, _ in friends]
    end_vars = [Int(f'end_{name}') for name, _, _, _, _ in friends]
    met = [Bool(f'met_{name}') for name, _, _, _, _ in friends]

    # Add basic meeting constraints
    for i, (_, _, avail_start, avail_end, min_dur) in enumerate(friends):
        s.add(Implies(met[i], start_vars[i] >= avail_start))
        s.add(Implies(met[i], end_vars[i] <= avail_end))
        s.add(Implies(met[i], end_vars[i] - start_vars[i] >= min_dur))

    # Travel time matrix (simplified for this example)
    travel_times = {
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "North Beach"): 18,
        # Add more travel times as needed
    }

    def get_travel_time(from_loc, to_loc):
        return travel_times.get((from_loc, to_loc), 0)

    # Add ordering constraints between meetings
    for i in range(len(friends)):
        for j in range(i+1, len(friends)):
            s.add(Implies(And(met[i], met[j]),
                         Or(end_vars[i] + get_travel_time(friends[i][1], friends[j][1]) <= start_vars[j],
                            end_vars[j] + get_travel_time(friends[j][1], friends[i][1]) <= start_vars[i])))

    # Starting point constraint
    current_location = "Presidio"
    current_time = 9 * 60
    for i in range(len(friends)):
        s.add(Implies(met[i], start_vars[i] >= current_time + get_travel_time(current_location, friends[i][1])))

    # Maximize number of meetings
    s.maximize(Sum([If(m, 1, 0) for m in met]))

    # Solve and print results
    if s.check() == sat:
        model = s.model()
        print("Optimal schedule found:")
        for i, (name, loc, _, _, _) in enumerate(friends):
            if is_true(model[met[i]]):
                start = model[start_vars[i]].as_long()
                end = model[end_vars[i]].as_long()
                print(f"Meet {name} at {loc} from {start//60:02d}:{start%60:02d} to {end//60:02d}:{end%60:02d}")
    else:
        print("No feasible schedule found")

solve_scheduling()