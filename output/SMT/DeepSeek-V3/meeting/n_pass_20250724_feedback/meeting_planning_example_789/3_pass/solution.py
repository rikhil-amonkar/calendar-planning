from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Optimize()

    # Define travel times (in minutes) between locations
    travel_times = {
        ('Union Square', 'Russian Hill'): 13,
        ('Union Square', 'Alamo Square'): 15,
        ('Union Square', 'Haight-Ashbury'): 18,
        ('Union Square', 'Marina District'): 18,
        ('Union Square', 'Bayview'): 15,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Presidio'): 24,
        ('Union Square', 'Sunset District'): 27,
        ('Russian Hill', 'Union Square'): 10,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'Marina District'): 7,
        ('Russian Hill', 'Bayview'): 23,
        ('Russian Hill', 'Chinatown'): 9,
        ('Russian Hill', 'Presidio'): 14,
        ('Russian Hill', 'Sunset District'): 23,
        ('Alamo Square', 'Union Square'): 14,
        ('Alamo Square', 'Russian Hill'): 13,
        ('Alamo Square', 'Haight-Ashbury'): 5,
        ('Alamo Square', 'Marina District'): 15,
        ('Alamo Square', 'Bayview'): 16,
        ('Alamo Square', 'Chinatown'): 15,
        ('Alamo Square', 'Presidio'): 17,
        ('Alamo Square', 'Sunset District'): 16,
        ('Haight-Ashbury', 'Union Square'): 19,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Haight-Ashbury', 'Alamo Square'): 5,
        ('Haight-Ashbury', 'Marina District'): 17,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Haight-Ashbury', 'Chinatown'): 19,
        ('Haight-Ashbury', 'Presidio'): 15,
        ('Haight-Ashbury', 'Sunset District'): 15,
        ('Marina District', 'Union Square'): 16,
        ('Marina District', 'Russian Hill'): 8,
        ('Marina District', 'Alamo Square'): 15,
        ('Marina District', 'Haight-Ashbury'): 16,
        ('Marina District', 'Bayview'): 27,
        ('Marina District', 'Chinatown'): 15,
        ('Marina District', 'Presidio'): 10,
        ('Marina District', 'Sunset District'): 19,
        ('Bayview', 'Union Square'): 18,
        ('Bayview', 'Russian Hill'): 23,
        ('Bayview', 'Alamo Square'): 16,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'Marina District'): 27,
        ('Bayview', 'Chinatown'): 19,
        ('Bayview', 'Presidio'): 32,
        ('Bayview', 'Sunset District'): 23,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'Russian Hill'): 7,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'Haight-Ashbury'): 19,
        ('Chinatown', 'Marina District'): 12,
        ('Chinatown', 'Bayview'): 20,
        ('Chinatown', 'Presidio'): 19,
        ('Chinatown', 'Sunset District'): 29,
        ('Presidio', 'Union Square'): 22,
        ('Presidio', 'Russian Hill'): 14,
        ('Presidio', 'Alamo Square'): 19,
        ('Presidio', 'Haight-Ashbury'): 15,
        ('Presidio', 'Marina District'): 11,
        ('Presidio', 'Bayview'): 31,
        ('Presidio', 'Chinatown'): 21,
        ('Presidio', 'Sunset District'): 15,
        ('Sunset District', 'Union Square'): 30,
        ('Sunset District', 'Russian Hill'): 24,
        ('Sunset District', 'Alamo Square'): 17,
        ('Sunset District', 'Haight-Ashbury'): 15,
        ('Sunset District', 'Marina District'): 21,
        ('Sunset District', 'Bayview'): 22,
        ('Sunset District', 'Chinatown'): 30,
        ('Sunset District', 'Presidio'): 16,
    }

    # Friends' data: name, location, available start, available end, min duration (in minutes)
    friends = [
        ('Betty', 'Russian Hill', 7*60, 16*60 + 45, 105),
        ('Melissa', 'Alamo Square', 9*60 + 30, 17*60 + 15, 105),
        ('Joshua', 'Haight-Ashbury', 12*60 + 15, 19*60, 90),
        ('Jeffrey', 'Marina District', 12*60 + 15, 18*60, 45),
        ('James', 'Bayview', 7*60 + 30, 20*60, 90),
        ('Anthony', 'Chinatown', 11*60 + 45, 13*60 + 30, 75),
        ('Timothy', 'Presidio', 12*60 + 30, 14*60 + 45, 90),
        ('Emily', 'Sunset District', 19*60 + 30, 21*60 + 30, 120),
    ]

    # Variables for each meeting
    meeting_vars = []
    scheduled = []  # Boolean variables indicating if meeting is scheduled
    for name, loc, avail_start, avail_end, min_dur in friends:
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        is_scheduled = Bool(f'scheduled_{name}')
        meeting_vars.append((name, loc, start, end, min_dur, avail_start, avail_end, is_scheduled))
        scheduled.append(is_scheduled)

    # Constraints for each meeting
    for name, loc, start, end, min_dur, avail_start, avail_end, is_scheduled in meeting_vars:
        # If scheduled, must fit in availability window
        s.add(Implies(is_scheduled, start >= avail_start))
        s.add(Implies(is_scheduled, end <= avail_end))
        s.add(Implies(is_scheduled, end == start + min_dur))

    # Initial location is Union Square at 9:00AM (540 minutes)
    current_time = 540
    current_loc = 'Union Square'

    # Create a list to hold the meeting order (only scheduled meetings)
    scheduled_meetings = [m for m in meeting_vars]

    # Add constraints for travel times between scheduled meetings
    for i in range(len(scheduled_meetings) - 1):
        name1, loc1, start1, end1, min_dur1, avail_start1, avail_end1, sched1 = scheduled_meetings[i]
        name2, loc2, start2, end2, min_dur2, avail_start2, avail_end2, sched2 = scheduled_meetings[i + 1]
        travel_time = travel_times.get((loc1, loc2), 60)
        # Only enforce if both meetings are scheduled
        s.add(Implies(And(sched1, sched2), start2 >= end1 + travel_time))

    # Constraint for first scheduled meeting - must be reachable from Union Square
    if len(scheduled_meetings) > 0:
        first_name, first_loc, first_start, first_end, first_min_dur, first_avail_start, first_avail_end, first_sched = scheduled_meetings[0]
        travel_time = travel_times.get((current_loc, first_loc), 60)
        s.add(Implies(first_sched, first_start >= current_time + travel_time))

    # Maximize the number of scheduled meetings
    s.maximize(Sum([If(s, 1, 0) for s in scheduled]))

    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for name, loc, start, end, min_dur, avail_start, avail_end, is_scheduled in scheduled_meetings:
            if is_true(m.evaluate(is_scheduled)):
                start_val = m.evaluate(start).as_long()
                end_val = m.evaluate(end).as_long()
                start_hh = start_val // 60
                start_mm = start_val % 60
                end_hh = end_val // 60
                end_mm = end_val % 60
                itinerary.append({
                    "action": "meet",
                    "person": name,
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
print("SOLUTION:")
print(json.dumps(solution, indent=2))