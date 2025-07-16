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

    # Create variables for each friend's meeting start and end times
    start_vars = []
    end_vars = []
    met = []
    for i, (name, loc, avail_start, avail_end, min_dur) in enumerate(friends):
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        is_met = Bool(f'met_{name}')
        s.add(Implies(is_met, start >= avail_start))
        s.add(Implies(is_met, end <= avail_end))
        s.add(Implies(is_met, end - start >= min_dur))
        start_vars.append(start)
        end_vars.append(end)
        met.append(is_met)

    # Define travel time matrix
    travel_times = {
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "North Beach"): 18,
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "Alamo Square"): 10,
        ("Pacific Heights", "Sunset District"): 21,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "North Beach"): 9,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Alamo Square"): 9,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Nob Hill"): 20,
        ("Golden Gate Park", "North Beach"): 23,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "Alamo Square"): 21,
        ("Fisherman's Wharf", "Sunset District"): 27,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "Fisherman's Wharf"): 10,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "North Beach"): 11,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Pacific Heights"): 10,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Fisherman's Wharf"): 19,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "North Beach"): 15,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Pacific Heights"): 21,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "Fisherman's Wharf"): 29,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Nob Hill"): 27,
        ("Sunset District", "North Beach"): 28,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Golden Gate Park"): 17,
        ("Nob Hill", "Fisherman's Wharf"): 10,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Sunset District"): 24,
        ("Nob Hill", "North Beach"): 8,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Pacific Heights"): 8,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Sunset District"): 27,
        ("North Beach", "Nob Hill"): 7
    }

    # Function to get travel time between two locations
    def get_travel_time(from_loc, to_loc):
        return travel_times.get((from_loc, to_loc), 0)

    # Add constraints for travel times between consecutive meetings
    for i in range(len(friends)):
        for j in range(len(friends)):
            if i != j:
                s.add(Implies(And(met[i], met[j]),
                             Or(end_vars[i] + get_travel_time(friends[i][1], friends[j][1]) <= start_vars[j],
                                end_vars[j] + get_travel_time(friends[j][1], friends[i][1]) <= start_vars[i])))

    # Constraint: Start at Presidio at 9:00 AM (540 minutes)
    current_location = "Presidio"
    current_time = 9 * 60
    for i in range(len(friends)):
        s.add(Implies(met[i], start_vars[i] >= current_time + get_travel_time(current_location, friends[i][1])))

    # Maximize the number of friends met
    s.maximize(Sum([If(m, 1, 0) for m in met]))

    # Check if a solution exists
    if s.check() == sat:
        model = s.model()
        print("Feasible schedule found. Meetings:")
        for i, (name, loc, _, _, _) in enumerate(friends):
            if model.evaluate(met[i]):
                start = model.evaluate(start_vars[i])
                end = model.evaluate(end_vars[i])
                start_h = start.as_long() // 60
                start_m = start.as_long() % 60
                end_h = end.as_long() // 60
                end_m = end.as_long() % 60
                print(f"{name}: {loc}, from {start_h:02d}:{start_m:02d} to {end_h:02d}:{end_m:02d}")
    else:
        print("No feasible schedule found.")

solve_scheduling()