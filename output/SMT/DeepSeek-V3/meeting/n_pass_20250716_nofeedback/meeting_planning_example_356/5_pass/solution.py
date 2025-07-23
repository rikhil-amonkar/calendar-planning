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
    barbara_end = 20 * 60 + 15    # 8:15 PM
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

    # Define variables for meeting times
    kimberly_start_var = Int('kimberly_start')
    kimberly_end_var = Int('kimberly_end')
    margaret_start_var = Int('margaret_start')
    margaret_end_var = Int('margaret_end')
    barbara_start_var = Int('barbara_start')
    barbara_end_var = Int('barbara_end')
    kevin_start_var = Int('kevin_start')
    kevin_end_var = Int('kevin_end')

    # Define whether we meet each person
    meet_kimberly = Bool('meet_kimberly')
    meet_margaret = Bool('meet_margaret')
    meet_barbara = Bool('meet_barbara')
    meet_kevin = Bool('meet_kevin')

    # Constraints for each possible meeting
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

    # Define the sequence of meetings
    # We'll model this as visiting locations in some order
    locations = ['Bayview', 'Union Square', 'Presidio', 'North Beach', 'Haight-Ashbury']
    arrival_times = {loc: Int(f'arrival_{loc}') for loc in locations}
    departure_times = {loc: Int(f'departure_{loc}') for loc in locations}

    # Initial condition: start at Bayview at 9:00 AM
    s.add(arrival_times['Bayview'] == start_time)
    s.add(departure_times['Bayview'] == start_time)

    # Define possible meeting orders using boolean variables
    # We'll create variables for each possible transition
    transitions = [
        ('Bayview', 'Union Square'),
        ('Bayview', 'Presidio'),
        ('Bayview', 'North Beach'),
        ('Bayview', 'Haight-Ashbury'),
        ('Union Square', 'Presidio'),
        ('Union Square', 'North Beach'),
        ('Union Square', 'Haight-Ashbury'),
        ('Presidio', 'Union Square'),
        ('Presidio', 'North Beach'),
        ('Presidio', 'Haight-Ashbury'),
        ('North Beach', 'Union Square'),
        ('North Beach', 'Presidio'),
        ('North Beach', 'Haight-Ashbury'),
        ('Haight-Ashbury', 'Union Square'),
        ('Haight-Ashbury', 'Presidio'),
        ('Haight-Ashbury', 'North Beach')
    ]

    # Create boolean variables for each possible transition
    transition_vars = {t: Bool(f'transition_{t[0]}_{t[1]}') for t in transitions}

    # Exactly one transition from Bayview
    s.add(Or(
        transition_vars[('Bayview', 'Union Square')],
        transition_vars[('Bayview', 'Presidio')],
        transition_vars[('Bayview', 'North Beach')],
        transition_vars[('Bayview', 'Haight-Ashbury')]
    ))

    # For each meeting location, define arrival and departure times
    for loc in ['Union Square', 'Presidio', 'North Beach', 'Haight-Ashbury']:
        # Arrival time is departure from previous location + travel time
        prev_locs = [prev for (prev, curr) in transitions if curr == loc]
        s.add(Or([
            And(
                transition_vars[(prev, loc)],
                arrival_times[loc] == departure_times[prev] + travel_times[(prev, loc)]
            )
            for prev in prev_locs
        ]))

        # Departure time is arrival time + meeting duration (if meeting happens)
        if loc == 'Union Square':
            s.add(departure_times[loc] == If(meet_kimberly, 
                arrival_times[loc] + meet_kimberly_duration, 
                arrival_times[loc]))
            s.add(Implies(meet_kimberly, arrival_times[loc] == kimberly_start_var))
        elif loc == 'Presidio':
            s.add(departure_times[loc] == If(meet_margaret, 
                arrival_times[loc] + meet_margaret_duration, 
                arrival_times[loc]))
            s.add(Implies(meet_margaret, arrival_times[loc] == margaret_start_var))
        elif loc == 'North Beach':
            s.add(departure_times[loc] == If(meet_barbara, 
                arrival_times[loc] + meet_barbara_duration, 
                arrival_times[loc]))
            s.add(Implies(meet_barbara, arrival_times[loc] == barbara_start_var))
        elif loc == 'Haight-Ashbury':
            s.add(departure_times[loc] == If(meet_kevin, 
                arrival_times[loc] + meet_kevin_duration, 
                arrival_times[loc]))
            s.add(Implies(meet_kevin, arrival_times[loc] == kevin_start_var))

    # Try to meet all friends first
    s.push()
    s.add(And(meet_kimberly, meet_margaret, meet_barbara, meet_kevin))
    
    if s.check() == sat:
        model = s.model()
        itinerary = []

        def add_to_itinerary(person, start_var, end_var):
            start = model[start_var].as_long()
            end = model[end_var].as_long()
            if start > 0 and end > 0:
                itinerary.append({
                    "action": "meet",
                    "person": person,
                    "start_time": f"{start//60:02d}:{start%60:02d}",
                    "end_time": f"{end//60:02d}:{end%60:02d}"
                })

        add_to_itinerary("Kimberly", kimberly_start_var, kimberly_end_var)
        add_to_itinerary("Margaret", margaret_start_var, margaret_end_var)
        add_to_itinerary("Barbara", barbara_start_var, barbara_end_var)
        add_to_itinerary("Kevin", kevin_start_var, kevin_end_var)

        # Sort by start time
        itinerary.sort(key=lambda x: x['start_time'])
        s.pop()
        return {"itinerary": itinerary}
    else:
        s.pop()
        # If we can't meet all, try meeting 3
        s.push()
        s.add(Or(
            And(meet_kimberly, meet_margaret, meet_barbara),
            And(meet_kimberly, meet_margaret, meet_kevin),
            And(meet_kimberly, meet_barbara, meet_kevin),
            And(meet_margaret, meet_barbara, meet_kevin)
        ))
        
        if s.check() == sat:
            model = s.model()
            itinerary = []

            def add_to_itinerary(person, start_var, end_var):
                start = model[start_var].as_long()
                end = model[end_var].as_long()
                if start > 0 and end > 0:
                    itinerary.append({
                        "action": "meet",
                        "person": person,
                        "start_time": f"{start//60:02d}:{start%60:02d}",
                        "end_time": f"{end//60:02d}:{end%60:02d}"
                    })

            add_to_itinerary("Kimberly", kimberly_start_var, kimberly_end_var)
            add_to_itinerary("Margaret", margaret_start_var, margaret_end_var)
            add_to_itinerary("Barbara", barbara_start_var, barbara_end_var)
            add_to_itinerary("Kevin", kevin_start_var, kevin_end_var)

            # Sort by start time
            itinerary.sort(key=lambda x: x['start_time'])
            s.pop()
            return {"itinerary": itinerary}
        else:
            s.pop()
            return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))