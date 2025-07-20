from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define time variables for each meeting and travel
    # We'll represent times in minutes since 9:00 AM (540 minutes since midnight)
    start_time = 540  # 9:00 AM in minutes

    # Meeting durations (in minutes)
    meet_barbara_duration = 60
    meet_margaret_duration = 30
    meet_kevin_duration = 30
    meet_kimberly_duration = 30

    # Available time windows for each friend (in minutes since midnight)
    barbara_start = 13 * 60 + 45  # 1:45 PM
    barbara_end = 20 * 60 + 15     # 8:15 PM
    margaret_start = 10 * 60 + 15  # 10:15 AM
    margaret_end = 15 * 60 + 15    # 3:15 PM
    kevin_start = 20 * 60          # 8:00 PM
    kevin_end = 20 * 60 + 45       # 8:45 PM
    kimberly_start = 7 * 60 + 45   # 7:45 AM
    kimberly_end = 16 * 60 + 45    # 4:45 PM

    # Travel times between locations (in minutes)
    travel_times = {
        ('Bayview', 'North Beach'): 21,
        ('Bayview', 'Presidio'): 31,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'Union Square'): 17,
        ('North Beach', 'Bayview'): 22,
        ('North Beach', 'Presidio'): 17,
        ('North Beach', 'Haight-Ashbury'): 18,
        ('North Beach', 'Union Square'): 7,
        ('Presidio', 'Bayview'): 31,
        ('Presidio', 'North Beach'): 18,
        ('Presidio', 'Haight-Ashbury'): 15,
        ('Presidio', 'Union Square'): 22,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Haight-Ashbury', 'North Beach'): 19,
        ('Haight-Ashbury', 'Presidio'): 15,
        ('Haight-Ashbury', 'Union Square'): 17,
        ('Union Square', 'Bayview'): 15,
        ('Union Square', 'North Beach'): 10,
        ('Union Square', 'Presidio'): 24,
        ('Union Square', 'Haight-Ashbury'): 18,
    }

    # Define variables for meeting each friend
    meet_barbara = Bool('meet_barbara')
    meet_margaret = Bool('meet_margaret')
    meet_kevin = Bool('meet_kevin')
    meet_kimberly = Bool('meet_kimberly')

    # Define start and end times for each possible meeting
    barbara_start_var = Int('barbara_start')
    barbara_end_var = Int('barbara_end')
    margaret_start_var = Int('margaret_start')
    margaret_end_var = Int('margaret_end')
    kevin_start_var = Int('kevin_start')
    kevin_end_var = Int('kevin_end')
    kimberly_start_var = Int('kimberly_start')
    kimberly_end_var = Int('kimberly_end')

    # Constraints for each meeting
    # Barbara (North Beach)
    s.add(Implies(meet_barbara, And(
        barbara_start_var >= barbara_start,
        barbara_end_var <= barbara_end,
        barbara_end_var == barbara_start_var + meet_barbara_duration
    )))
    s.add(Implies(Not(meet_barbara), And(
        barbara_start_var == 0,
        barbara_end_var == 0
    )))

    # Margaret (Presidio)
    s.add(Implies(meet_margaret, And(
        margaret_start_var >= margaret_start,
        margaret_end_var <= margaret_end,
        margaret_end_var == margaret_start_var + meet_margaret_duration
    )))
    s.add(Implies(Not(meet_margaret), And(
        margaret_start_var == 0,
        margaret_end_var == 0
    )))

    # Kevin (Haight-Ashbury)
    s.add(Implies(meet_kevin, And(
        kevin_start_var >= kevin_start,
        kevin_end_var <= kevin_end,
        kevin_end_var == kevin_start_var + meet_kevin_duration
    )))
    s.add(Implies(Not(meet_kevin), And(
        kevin_start_var == 0,
        kevin_end_var == 0
    )))

    # Kimberly (Union Square)
    s.add(Implies(meet_kimberly, And(
        kimberly_start_var >= kimberly_start,
        kimberly_end_var <= kimberly_end,
        kimberly_end_var == kimberly_start_var + meet_kimberly_duration
    )))
    s.add(Implies(Not(meet_kimberly), And(
        kimberly_start_var == 0,
        kimberly_end_var == 0
    )))

    # Define the order of meetings
    # We'll use integers to represent the sequence
    order = [Int(f'order_{i}') for i in range(4)]
    for i in range(4):
        s.add(And(order[i] >= 0, order[i] < 4))
    s.add(Distinct(order))

    # Create variables for arrival and departure times at each location
    locations = ['Bayview', 'North Beach', 'Presidio', 'Haight-Ashbury', 'Union Square']
    arrival_times = {loc: Int(f'arrival_{loc}') for loc in locations}
    departure_times = {loc: Int(f'departure_{loc}') for loc in locations}

    # Initial condition: start at Bayview at 9:00 AM
    s.add(arrival_times['Bayview'] == start_time)
    s.add(departure_times['Bayview'] == start_time)

    # For each meeting location, set arrival and departure times
    for loc in ['North Beach', 'Presidio', 'Haight-Ashbury', 'Union Square']:
        # Arrival time is departure from previous location + travel time
        # We need to consider all possible previous locations
        prev_locs = [l for l in locations if l != loc]
        s.add(Or([
            And(
                arrival_times[loc] == departure_times[prev_loc] + travel_times[(prev_loc, loc)],
                arrival_times[loc] > departure_times[prev_loc]
            )
            for prev_loc in prev_locs
        ]))

        # Departure time is arrival time + meeting duration (if meeting happens)
        if loc == 'North Beach':
            s.add(departure_times[loc] == If(meet_barbara, 
                arrival_times[loc] + meet_barbara_duration, 
                arrival_times[loc]))
        elif loc == 'Presidio':
            s.add(departure_times[loc] == If(meet_margaret, 
                arrival_times[loc] + meet_margaret_duration, 
                arrival_times[loc]))
        elif loc == 'Haight-Ashbury':
            s.add(departure_times[loc] == If(meet_kevin, 
                arrival_times[loc] + meet_kevin_duration, 
                arrival_times[loc]))
        elif loc == 'Union Square':
            s.add(departure_times[loc] == If(meet_kimberly, 
                arrival_times[loc] + meet_kimberly_duration, 
                arrival_times[loc]))

    # Ensure meeting times match the scheduled times
    s.add(Implies(meet_barbara, barbara_start_var == arrival_times['North Beach']))
    s.add(Implies(meet_margaret, margaret_start_var == arrival_times['Presidio']))
    s.add(Implies(meet_kevin, kevin_start_var == arrival_times['Haight-Ashbury']))
    s.add(Implies(meet_kimberly, kimberly_start_var == arrival_times['Union Square']))

    # Objective: maximize the number of friends met
    num_met = Int('num_met')
    s.add(num_met == 
          If(meet_barbara, 1, 0) + 
          If(meet_margaret, 1, 0) + 
          If(meet_kevin, 1, 0) + 
          If(meet_kimberly, 1, 0))
    
    # Try to meet all friends first
    s.push()
    s.add(num_met == 4)
    if s.check() == sat:
        model = s.model()
        itinerary = []

        # Helper function to convert minutes to HH:MM
        def min_to_time(minutes):
            hh = minutes // 60
            mm = minutes % 60
            return f"{hh:02d}:{mm:02d}"

        # Add meetings to itinerary if they happened
        if is_true(model[meet_kimberly]):
            itinerary.append({
                "action": "meet",
                "person": "Kimberly",
                "start_time": min_to_time(model[kimberly_start_var].as_long()),
                "end_time": min_to_time(model[kimberly_end_var].as_long())
            })

        if is_true(model[meet_margaret]):
            itinerary.append({
                "action": "meet",
                "person": "Margaret",
                "start_time": min_to_time(model[margaret_start_var].as_long()),
                "end_time": min_to_time(model[margaret_end_var].as_long())
            })

        if is_true(model[meet_barbara]):
            itinerary.append({
                "action": "meet",
                "person": "Barbara",
                "start_time": min_to_time(model[barbara_start_var].as_long()),
                "end_time": min_to_time(model[barbara_end_var].as_long())
            })

        if is_true(model[meet_kevin]):
            itinerary.append({
                "action": "meet",
                "person": "Kevin",
                "start_time": min_to_time(model[kevin_start_var].as_long()),
                "end_time": min_to_time(model[kevin_end_var].as_long())
            })

        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x['start_time'])
        s.pop()
        return {"itinerary": itinerary}
    else:
        s.pop()
        # If we can't meet all friends, try meeting 3
        s.push()
        s.add(num_met == 3)
        if s.check() == sat:
            model = s.model()
            itinerary = []

            def min_to_time(minutes):
                hh = minutes // 60
                mm = minutes % 60
                return f"{hh:02d}:{mm:02d}"

            if is_true(model[meet_kimberly]):
                itinerary.append({
                    "action": "meet",
                    "person": "Kimberly",
                    "start_time": min_to_time(model[kimberly_start_var].as_long()),
                    "end_time": min_to_time(model[kimberly_end_var].as_long())
                })

            if is_true(model[meet_margaret]):
                itinerary.append({
                    "action": "meet",
                    "person": "Margaret",
                    "start_time": min_to_time(model[margaret_start_var].as_long()),
                    "end_time": min_to_time(model[margaret_end_var].as_long())
                })

            if is_true(model[meet_barbara]):
                itinerary.append({
                    "action": "meet",
                    "person": "Barbara",
                    "start_time": min_to_time(model[barbara_start_var].as_long()),
                    "end_time": min_to_time(model[barbara_end_var].as_long())
                })

            if is_true(model[meet_kevin]):
                itinerary.append({
                    "action": "meet",
                    "person": "Kevin",
                    "start_time": min_to_time(model[kevin_start_var].as_long()),
                    "end_time": min_to_time(model[kevin_end_var].as_long())
                })

            # Sort itinerary by start time
            itinerary.sort(key=lambda x: x['start_time'])
            s.pop()
            return {"itinerary": itinerary}
        else:
            s.pop()
            return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))