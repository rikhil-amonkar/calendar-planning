from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define time variables for each meeting
    # Sarah at Fisherman's Wharf: 2:45PM to 5:30PM, min 105 minutes (1.75 hours)
    sarah_start = Real('sarah_start')
    sarah_end = Real('sarah_end')
    s.add(sarah_start >= 14.75)  # 2:45PM is 14.75
    s.add(sarah_end <= 17.5)     # 5:30PM is 17.5
    s.add(sarah_end - sarah_start >= 1.75)

    # Mary at Richmond District: 1:00PM to 7:15PM, min 75 minutes (1.25 hours)
    mary_start = Real('mary_start')
    mary_end = Real('mary_end')
    s.add(mary_start >= 13.0)    # 1:00PM is 13.0
    s.add(mary_end <= 19.25)     # 7:15PM is 19.25
    s.add(mary_end - mary_start >= 1.25)

    # Helen at Mission District: 9:45PM to 10:30PM, min 30 minutes (0.5 hours)
    helen_start = Real('helen_start')
    helen_end = Real('helen_end')
    s.add(helen_start >= 21.75)  # 9:45PM is 21.75
    s.add(helen_end <= 22.5)     # 10:30PM is 22.5
    s.add(helen_end - helen_start >= 0.5)

    # Thomas at Bayview: 3:15PM to 6:45PM, min 120 minutes (2 hours)
    thomas_start = Real('thomas_start')
    thomas_end = Real('thomas_end')
    s.add(thomas_start >= 15.25)  # 3:15PM is 15.25
    s.add(thomas_end <= 18.75)    # 6:45PM is 18.75
    s.add(thomas_end - thomas_start >= 2.0)

    # Travel times (in hours)
    travel = {
        'Haight-Ashbury': {
            'Fisherman\'s Wharf': 23/60,
            'Richmond District': 10/60,
            'Mission District': 11/60,
            'Bayview': 18/60
        },
        'Fisherman\'s Wharf': {
            'Haight-Ashbury': 22/60,
            'Richmond District': 18/60,
            'Mission District': 22/60,
            'Bayview': 26/60
        },
        'Richmond District': {
            'Haight-Ashbury': 10/60,
            'Fisherman\'s Wharf': 18/60,
            'Mission District': 20/60,
            'Bayview': 26/60
        },
        'Mission District': {
            'Haight-Ashbury': 12/60,
            'Fisherman\'s Wharf': 22/60,
            'Richmond District': 20/60,
            'Bayview': 15/60
        },
        'Bayview': {
            'Haight-Ashbury': 19/60,
            'Fisherman\'s Wharf': 25/60,
            'Richmond District': 25/60,
            'Mission District': 13/60
        }
    }

    # Define meeting sequence variables
    # We'll model the schedule as visiting friends in a particular order
    # with appropriate travel times between locations
    
    # Start at Haight-Ashbury at 9:00
    current_time = 9.0
    current_loc = 'Haight-Ashbury'

    # Possible meeting order: Mary -> Sarah -> Thomas -> Helen
    # Mary first
    s.add(mary_start >= current_time + travel[current_loc]['Richmond District'])
    current_time = mary_end
    current_loc = 'Richmond District'

    # Then Sarah
    s.add(sarah_start >= current_time + travel[current_loc]['Fisherman\'s Wharf'])
    current_time = sarah_end
    current_loc = 'Fisherman\'s Wharf'

    # Then Thomas
    s.add(thomas_start >= current_time + travel[current_loc]['Bayview'])
    current_time = thomas_end
    current_loc = 'Bayview'

    # Finally Helen
    s.add(helen_start >= current_time + travel[current_loc]['Mission District'])

    # Ensure no overlapping meetings
    s.add(mary_end <= sarah_start)
    s.add(sarah_end <= thomas_start)
    s.add(thomas_end <= helen_start)

    # Check if the schedule is feasible
    if s.check() == sat:
        model = s.model()
        
        # Helper function to convert fractional hours to HH:MM
        def to_hhmm(val):
            val = model[val].as_fraction()
            hours = val.numerator // val.denominator
            minutes = (val.numerator % val.denominator) * 60 // val.denominator
            return f"{hours:02d}:{minutes:02d}"
        
        # Collect all meetings with their times
        itinerary = [
            {"action": "meet", "person": "Mary", "start_time": to_hhmm(mary_start), "end_time": to_hhmm(mary_end)},
            {"action": "meet", "person": "Sarah", "start_time": to_hhmm(sarah_start), "end_time": to_hhmm(sarah_end)},
            {"action": "meet", "person": "Thomas", "start_time": to_hhmm(thomas_start), "end_time": to_hhmm(thomas_end)},
            {"action": "meet", "person": "Helen", "start_time": to_hhmm(helen_start), "end_time": to_hhmm(helen_end)}
        ]
        
        # Sort by start time
        itinerary.sort(key=lambda x: x["start_time"])
        
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))