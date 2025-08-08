from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    solver = Solver()

    # Define locations and their indices
    locations = {
        'Golden Gate Park': 0,
        'Fisherman\'s Wharf': 1,
        'Bayview': 2,
        'Mission District': 3,
        'Embarcadero': 4,
        'Financial District': 5
    }

    # Travel times in minutes between locations
    travel_times = [
        [0, 24, 23, 17, 25, 26],  # From Golden Gate Park
        [25, 0, 26, 22, 8, 11],    # From Fisherman's Wharf
        [22, 25, 0, 13, 19, 19],   # From Bayview
        [17, 22, 15, 0, 19, 17],   # From Mission District
        [25, 6, 21, 20, 0, 5],     # From Embarcadero
        [23, 10, 19, 17, 4, 0]     # From Financial District
    ]

    # Friends and their constraints (times in minutes since midnight)
    friends = {
        'Barbara': {
            'location': 'Financial District',
            'start': 10*60 + 30,  # 10:30 AM
            'end': 16*60 + 30,    # 4:30 PM
            'duration': 15,
            'must_meet': True
        },
        'Kevin': {
            'location': 'Mission District',
            'start': 11*60 + 15,  # 11:15 AM
            'end': 15*60 + 15,   # 3:15 PM
            'duration': 30,
            'must_meet': True
        },
        'Joseph': {
            'location': 'Fisherman\'s Wharf',
            'start': 8*60,       # 8:00 AM
            'end': 17*60 + 30,    # 5:30 PM
            'duration': 90,
            'must_meet': True
        },
        'Jeffrey': {
            'location': 'Bayview',
            'start': 17*60 + 30,  # 5:30 PM
            'end': 21*60 + 30,   # 9:30 PM
            'duration': 60,
            'must_meet': True
        }
    }

    # Create variables for each meeting
    meet_vars = {}
    for person in friends:
        meet_vars[person] = {
            'start': Int(f'start_{person}'),
            'end': Int(f'end_{person}'),
            'location': locations[friends[person]['location']],
            'met': Bool(f'met_{person}')
        }

    # Starting at Golden Gate Park at 9:00 AM (540 minutes)
    current_time = 540
    current_location = locations['Golden Gate Park']

    # We'll try to meet friends in this order
    meeting_order = ['Barbara', 'Kevin', 'Joseph', 'Jeffrey']

    # Track previous meeting end time and location
    prev_end = Int('initial_time')
    solver.add(prev_end == current_time)
    prev_loc = Int('initial_loc')
    solver.add(prev_loc == current_location)

    for person in meeting_order:
        info = friends[person]
        start_var = meet_vars[person]['start']
        end_var = meet_vars[person]['end']
        loc = meet_vars[person]['location']
        met_var = meet_vars[person]['met']

        # If we meet this person
        solver.add(Implies(met_var, start_var >= info['start']))
        solver.add(Implies(met_var, end_var <= info['end']))
        solver.add(Implies(met_var, end_var == start_var + info['duration']))
        
        # Create travel time constraints using If expressions
        travel_time = Int(f'travel_{person}')
        solver.add(travel_time == travel_times[current_location][loc])  # Initial travel time
        
        # More accurate travel time calculation
        for src in range(len(travel_times)):
            for dst in range(len(travel_times[0])):
                solver.add(If(And(prev_loc == src, met_var), 
                           travel_time == travel_times[src][dst], 
                           True))

        solver.add(Implies(met_var, start_var >= prev_end + travel_time))

        # Update previous end time and location if we meet this person
        new_prev_end = If(met_var, end_var, prev_end)
        new_prev_loc = If(met_var, loc, prev_loc)
        prev_end = new_prev_end
        prev_loc = new_prev_loc

    # We must meet all friends
    for person in friends:
        solver.add(meet_vars[person]['met'])

    # Try to find a solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for person in meeting_order:
            if is_true(model[meet_vars[person]['met']]):
                start = model[meet_vars[person]['start']].as_long()
                end = model[meet_vars[person]['end']].as_long()
                start_time = f"{start // 60:02d}:{start % 60:02d}"
                end_time = f"{end // 60:02d}:{end % 60:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": person,
                    "start_time": start_time,
                    "end_time": end_time
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x['start_time'])
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))