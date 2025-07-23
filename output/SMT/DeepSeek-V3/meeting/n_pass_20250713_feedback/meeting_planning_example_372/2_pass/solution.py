from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Locations
    locations = ['Sunset', 'Alamo', 'Russian', 'Golden', 'Mission']
    loc_to_idx = {loc: idx for idx, loc in enumerate(locations)}

    # Travel times matrix (minutes)
    travel_times = [
        [0, 17, 24, 11, 24],    # Sunset to others
        [16, 0, 13, 9, 10],     # Alamo to others
        [23, 15, 0, 21, 16],     # Russian to others
        [10, 10, 19, 0, 17],     # Golden to others
        [24, 11, 15, 17, 0]      # Mission to others
    ]

    # Convert travel times to hours for easier handling
    travel_hours = [[Real(f'travel_{i}_{j}') for j in range(5)] for i in range(5)]
    for i in range(5):
        for j in range(5):
            s.add(travel_hours[i][j] == travel_times[i][j] / 60.0)

    # Time variables for each location (arrival and departure)
    arrival = [Real(f'arrival_{loc}') for loc in locations]
    departure = [Real(f'departure_{loc}') for loc in locations]

    # Initial constraints: start at Sunset at 9:00 AM (9.0 hours)
    s.add(arrival[loc_to_idx['Sunset']] == 9.0)
    s.add(departure[loc_to_idx['Sunset']] >= arrival[loc_to_idx['Sunset']])

    # Meeting constraints
    # Charles at Alamo: 6:00 PM to 8:45 PM (18.0 to 20.75 hours), min 90 mins (1.5 hours)
    s.add(arrival[loc_to_idx['Alamo']] >= 18.0)
    s.add(departure[loc_to_idx['Alamo']] <= 20.75)
    s.add(departure[loc_to_idx['Alamo']] - arrival[loc_to_idx['Alamo']] >= 1.5)

    # Margaret at Russian: 9:00 AM to 4:00 PM (9.0 to 16.0 hours), min 30 mins (0.5 hours)
    s.add(arrival[loc_to_idx['Russian']] >= 9.0)
    s.add(departure[loc_to_idx['Russian']] <= 16.0)
    s.add(departure[loc_to_idx['Russian']] - arrival[loc_to_idx['Russian']] >= 0.5)

    # Daniel at Golden: 8:00 AM to 1:30 PM (8.0 to 13.5 hours), min 15 mins (0.25 hours)
    s.add(arrival[loc_to_idx['Golden']] >= 8.0)
    s.add(departure[loc_to_idx['Golden']] <= 13.5)
    s.add(departure[loc_to_idx['Golden']] - arrival[loc_to_idx['Golden']] >= 0.25)

    # Stephanie at Mission: 8:30 PM to 10:00 PM (20.5 to 22.0 hours), min 90 mins (1.5 hours)
    s.add(arrival[loc_to_idx['Mission']] >= 20.5)
    s.add(departure[loc_to_idx['Mission']] <= 22.0)
    s.add(departure[loc_to_idx['Mission']] - arrival[loc_to_idx['Mission']] >= 1.5)

    # Sequence constraints: ensure travel times are respected
    # Assume order: Sunset -> Russian -> Golden -> Alamo -> Mission
    s.add(arrival[loc_to_idx['Russian']] >= departure[loc_to_idx['Sunset']] + travel_hours[loc_to_idx['Sunset']][loc_to_idx['Russian']])
    s.add(arrival[loc_to_idx['Golden']] >= departure[loc_to_idx['Russian']] + travel_hours[loc_to_idx['Russian']][loc_to_idx['Golden']])
    s.add(arrival[loc_to_idx['Alamo']] >= departure[loc_to_idx['Golden']] + travel_hours[loc_to_idx['Golden']][loc_to_idx['Alamo']])
    s.add(arrival[loc_to_idx['Mission']] >= departure[loc_to_idx['Alamo']] + travel_hours[loc_to_idx['Alamo']][loc_to_idx['Mission']])

    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        print("Found a valid schedule:")
        for loc in locations:
            idx = loc_to_idx[loc]
            arr = m.evaluate(arrival[idx])
            dep = m.evaluate(departure[idx])
            # Convert fractional hours to HH:MM format
            def to_hhmm(h):
                if isinstance(h, RatNumRef):
                    h_val = h.numerator_as_long() / h.denominator_as_long()
                else:
                    h_val = float(h)
                hours = int(h_val)
                minutes = int((h_val - hours) * 60)
                return f"{hours:02d}:{minutes:02d}"
            print(f"{loc}: Arrive at {to_hhmm(arr)}, Depart at {to_hhmm(dep)}")
    else:
        print("No valid schedule found.")

solve_scheduling()