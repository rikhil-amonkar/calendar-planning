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
        'David': {
            'location': 'Embarcadero',
            'start': 8*60 + 15,  # 8:15 AM
            'end': 9*60,         # 9:00 AM
            'duration': 30
        },
        'Barbara': {
            'location': 'Financial District',
            'start': 10*60 + 30,  # 10:30 AM
            'end': 16*60 + 30,    # 4:30 PM
            'duration': 15
        },
        'Kevin': {
            'location': 'Mission District',
            'start': 11*60 + 15,  # 11:15 AM
            'end': 15*60 + 15,   # 3:15 PM
            'duration': 30
        },
        'Joseph': {
            'location': 'Fisherman\'s Wharf',
            'start': 8*60,       # 8:00 AM
            'end': 17*60 + 30,    # 5:30 PM
            'duration': 90
        },
        'Jeffrey': {
            'location': 'Bayview',
            'start': 17*60 + 30,  # 5:30 PM
            'end': 21*60 + 30,   # 9:30 PM
            'duration': 60
        }
    }

    # Create variables for each meeting
    meet_vars = {}
    for person in friends:
        meet_vars[person] = {
            'start': Int(f'start_{person}'),
            'end': Int(f'end_{person}'),
            'location': locations[friends[person]['location']]
        }

    # Initial state: starting at Golden Gate Park at 9:00 AM (540 minutes)
    current_time = 540
    current_location = locations['Golden Gate Park']

    # Define the order in which we'll try to meet friends
    meeting_order = ['David', 'Barbara', 'Kevin', 'Joseph', 'Jeffrey']

    # Add constraints for each meeting in order
    for person in meeting_order:
        info = friends[person]
        start_var = meet_vars[person]['start']
        end_var = meet_vars[person]['end']
        loc = meet_vars[person]['location']

        # Meeting must be within friend's availability
        solver.add(start_var >= info['start'])
        solver.add(end_var <= info['end'])
        solver.add(end_var == start_var + info['duration'])

        # Travel time from current location to friend's location
        travel_time = travel_times[current_location][loc]
        solver.add(start_var >= current_time + travel_time)

        # Update current time and location after meeting
        current_time = end_var
        current_location = loc

    # Add constraints to ensure we can meet all friends
    # This includes ensuring we have enough time between meetings
    for i in range(len(meeting_order) - 1):
        person1 = meeting_order[i]
        person2 = meeting_order[i + 1]
        travel_time = travel_times[meet_vars[person1]['location']][meet_vars[person2]['location']]
        solver.add(meet_vars[person2]['start'] >= meet_vars[person1]['end'] + travel_time)

    # Try to find a solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for person in meeting_order:
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
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))