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

    # Define variables for meeting start times
    barbara_start_var = Int('barbara_start')
    margaret_start_var = Int('margaret_start')
    kevin_start_var = Int('kevin_start')
    kimberly_start_var = Int('kimberly_start')

    # Define whether we meet each person (boolean)
    meet_barbara = Bool('meet_barbara')
    meet_margaret = Bool('meet_margaret')
    meet_kevin = Bool('meet_kevin')
    meet_kimberly = Bool('meet_kimberly')

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

    # Define the order of meetings and travel between them
    # We'll model this as a sequence of locations with travel times between them
    # For simplicity, we'll assume we can meet at most 4 friends in some order

    # Define possible meeting orders (permutations of the 4 friends)
    # We'll create variables to represent the order
    order = [Int(f'order_{i}') for i in range(4)]
    for i in range(4):
        s.add(And(order[i] >= 0, order[i] < 4))
    s.add(Distinct(order))

    # Create variables for each step's location, start time, and end time
    steps = []
    for i in range(5):  # 4 meetings + initial location
        steps.append({
            'location': String(f'step_{i}_location'),
            'arrival_time': Int(f'step_{i}_arrival'),
            'departure_time': Int(f'step_{i}_departure')
        })

    # Initial condition: start at Bayview at 9:00 AM
    s.add(steps[0]['location'] == 'Bayview')
    s.add(steps[0]['arrival_time'] == start_time)
    s.add(steps[0]['departure_time'] == start_time)

    # For each meeting step, determine which friend is being met and add constraints
    for i in range(1, 5):
        # Determine which friend is being met at this step
        current_order = order[i-1]
        s.add(Or(
            And(current_order == 0, steps[i]['location'] == 'North Beach'),
            And(current_order == 1, steps[i]['location'] == 'Presidio'),
            And(current_order == 2, steps[i]['location'] == 'Haight-Ashbury'),
            And(current_order == 3, steps[i]['location'] == 'Union Square')
        ))

        # Add travel time constraint from previous location
        travel_time = Int(f'travel_{i}')
        s.add(travel_time >= 0)
        for prev_loc in ['Bayview', 'North Beach', 'Presidio', 'Haight-Ashbury', 'Union Square']:
            for curr_loc in ['North Beach', 'Presidio', 'Haight-Ashbury', 'Union Square']:
                s.add(Implies(
                    And(steps[i-1]['location'] == prev_loc, steps[i]['location'] == curr_loc),
                    travel_time == travel_times[(prev_loc, curr_loc)]
                ))

        s.add(steps[i]['arrival_time'] == steps[i-1]['departure_time'] + travel_time)

        # Add meeting duration constraints based on who we're meeting
        meeting_duration = Int(f'meeting_duration_{i}')
        s.add(Or(
            And(steps[i]['location'] == 'North Beach', meeting_duration == meet_barbara_duration),
            And(steps[i]['location'] == 'Presidio', meeting_duration == meet_margaret_duration),
            And(steps[i]['location'] == 'Haight-Ashbury', meeting_duration == meet_kevin_duration),
            And(steps[i]['location'] == 'Union Square', meeting_duration == meet_kimberly_duration)
        ))

        s.add(steps[i]['departure_time'] == steps[i]['arrival_time'] + meeting_duration)

        # Add time window constraints for each friend
        s.add(Implies(
            steps[i]['location'] == 'North Beach',
            And(
                steps[i]['arrival_time'] >= barbara_start,
                steps[i]['departure_time'] <= barbara_end
            )
        ))
        s.add(Implies(
            steps[i]['location'] == 'Presidio',
            And(
                steps[i]['arrival_time'] >= margaret_start,
                steps[i]['departure_time'] <= margaret_end
            )
        ))
        s.add(Implies(
            steps[i]['location'] == 'Haight-Ashbury',
            And(
                steps[i]['arrival_time'] >= kevin_start,
                steps[i]['departure_time'] <= kevin_end
            )
        ))
        s.add(Implies(
            steps[i]['location'] == 'Union Square',
            And(
                steps[i]['arrival_time'] >= kimberly_start,
                steps[i]['departure_time'] <= kimberly_end
            )
        ))

    # Add constraints to ensure we don't meet the same friend twice
    s.add(Distinct([steps[i]['location'] for i in range(1, 5)]))

    # Objective: maximize the number of friends met
    num_met = Int('num_met')
    s.add(num_met == Sum([
        If(steps[1]['location'] == 'North Beach', 1, 0) +
        If(steps[2]['location'] == 'North Beach', 1, 0) +
        If(steps[3]['location'] == 'North Beach', 1, 0) +
        If(steps[4]['location'] == 'North Beach', 1, 0),
        If(steps[1]['location'] == 'Presidio', 1, 0) +
        If(steps[2]['location'] == 'Presidio', 1, 0) +
        If(steps[3]['location'] == 'Presidio', 1, 0) +
        If(steps[4]['location'] == 'Presidio', 1, 0),
        If(steps[1]['location'] == 'Haight-Ashbury', 1, 0) +
        If(steps[2]['location'] == 'Haight-Ashbury', 1, 0) +
        If(steps[3]['location'] == 'Haight-Ashbury', 1, 0) +
        If(steps[4]['location'] == 'Haight-Ashbury', 1, 0),
        If(steps[1]['location'] == 'Union Square', 1, 0) +
        If(steps[2]['location'] == 'Union Square', 1, 0) +
        If(steps[3]['location'] == 'Union Square', 1, 0) +
        If(steps[4]['location'] == 'Union Square', 1, 0)
    ]))

    # Try to maximize the number of friends met
    maximize_num_met = num_met == 4
    s.add(maximize_num_met)

    # Check if a solution exists
    if s.check() == sat:
        model = s.model()
        itinerary = []

        # Extract meeting information from the model
        for i in range(1, 5):
            loc = str(model[steps[i]['location']])
            start_min = model[steps[i]['arrival_time']].as_long()
            end_min = model[steps[i]['departure_time']].as_long()

            # Convert minutes to HH:MM format
            start_hh = start_min // 60
            start_mm = start_min % 60
            end_hh = end_min // 60
            end_mm = end_min % 60

            # Determine which friend is at this location
            person = ""
            if loc == 'North Beach':
                person = "Barbara"
            elif loc == 'Presidio':
                person = "Margaret"
            elif loc == 'Haight-Ashbury':
                person = "Kevin"
            elif loc == 'Union Square':
                person = "Kimberly"

            itinerary.append({
                "action": "meet",
                "person": person,
                "start_time": f"{start_hh:02d}:{start_mm:02d}",
                "end_time": f"{end_hh:02d}:{end_mm:02d}"
            })

        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x['start_time'])

        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))