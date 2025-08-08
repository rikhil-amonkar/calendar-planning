from z3 import *
import json

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define locations and their indices
    locations = {
        'Fisherman\'s Wharf': 0,
        'The Castro': 1,
        'Golden Gate Park': 2,
        'Embarcadero': 3,
        'Russian Hill': 4,
        'Nob Hill': 5,
        'Alamo Square': 6,
        'North Beach': 7
    }

    # Travel times between locations (in minutes)
    travel_times = [
        [0, 26, 25, 8, 7, 11, 20, 6],    # Fisherman's Wharf
        [24, 0, 11, 22, 18, 16, 8, 20],   # The Castro
        [24, 13, 0, 25, 19, 20, 10, 24],  # Golden Gate Park
        [6, 25, 25, 0, 8, 10, 19, 5],     # Embarcadero
        [7, 21, 21, 8, 0, 5, 15, 5],      # Russian Hill
        [11, 17, 17, 9, 5, 0, 11, 8],     # Nob Hill
        [19, 8, 9, 17, 13, 11, 0, 15],    # Alamo Square
        [5, 22, 22, 6, 4, 7, 16, 0]        # North Beach
    ]

    # Friends and their constraints
    friends = [
        {'name': 'Laura', 'location': 'The Castro', 'start': (19, 45), 'end': (21, 30), 'duration': 105},
        {'name': 'Daniel', 'location': 'Golden Gate Park', 'start': (21, 15), 'end': (21, 45), 'duration': 15},
        {'name': 'William', 'location': 'Embarcadero', 'start': (7, 0), 'end': (9, 0), 'duration': 90},
        {'name': 'Karen', 'location': 'Russian Hill', 'start': (14, 30), 'end': (19, 45), 'duration': 30},
        {'name': 'Stephanie', 'location': 'Nob Hill', 'start': (7, 30), 'end': (9, 30), 'duration': 45},
        {'name': 'Joseph', 'location': 'Alamo Square', 'start': (11, 30), 'end': (12, 45), 'duration': 15},
        {'name': 'Kimberly', 'location': 'North Beach', 'start': (15, 45), 'end': (19, 15), 'duration': 30}
    ]

    # Convert time to minutes since 00:00
    def time_to_minutes(time_tuple):
        return time_tuple[0] * 60 + time_tuple[1]

    # Convert minutes back to HH:MM format
    def minutes_to_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"

    # Create variables for each meeting
    meeting_vars = []
    for friend in friends:
        start_var = Int(f"start_{friend['name']}")
        end_var = Int(f"end_{friend['name']}")
        meeting_vars.append((friend, start_var, end_var))

    # Add basic constraints for each meeting
    for friend, start, end in meeting_vars:
        friend_start = time_to_minutes(friend['start'])
        friend_end = time_to_minutes(friend['end'])
        s.add(start >= friend_start)
        s.add(end <= friend_end)
        s.add(end - start >= friend['duration'])

    # Starting point: Fisherman's Wharf at 9:00 AM (540 minutes)
    current_time = 540
    current_loc = locations['Fisherman\'s Wharf']

    # Create an order for meetings to help the solver
    meeting_order = []
    for i, (friend, start, end) in enumerate(meeting_vars):
        meeting_order.append((start, end, friend['location']))
        
        # Add travel time from current location
        loc = locations[friend['location']]
        travel_time = travel_times[current_loc][loc]
        s.add(start >= current_time + travel_time)
        
        # Update current time and location after meeting
        current_time = end
        current_loc = loc

    # Ensure no overlapping meetings
    for i in range(len(meeting_vars)):
        for j in range(i + 1, len(meeting_vars)):
            _, start1, end1 = meeting_vars[i]
            _, start2, end2 = meeting_vars[j]
            s.add(Or(
                end1 <= start2,
                end2 <= start1
            ))

    # Prioritize critical meetings (Laura and Daniel)
    for friend, start, end in meeting_vars:
        if friend['name'] in ['Laura', 'Daniel']:
            s.add(start == time_to_minutes(friend['start']))

    # Try to solve
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for friend, start_var, end_var in meeting_vars:
            start_val = model[start_var].as_long()
            end_val = model[end_var].as_long()
            itinerary.append({
                "action": "meet",
                "person": friend['name'],
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })
        # Sort by start time
        itinerary.sort(key=lambda x: x['start_time'])
        return {"itinerary": itinerary}
    else:
        # If no solution found, try relaxing constraints
        s.reset()
        # Remove strict time constraints for Laura and Daniel
        for friend, start, end in meeting_vars:
            friend_start = time_to_minutes(friend['start'])
            friend_end = time_to_minutes(friend['end'])
            s.add(start >= friend_start)
            s.add(end <= friend_end)
            s.add(end - start >= friend['duration'])
        
        if s.check() == sat:
            model = s.model()
            itinerary = []
            for friend, start_var, end_var in meeting_vars:
                start_val = model[start_var].as_long()
                end_val = model[end_var].as_long()
                itinerary.append({
                    "action": "meet",
                    "person": friend['name'],
                    "start_time": minutes_to_time(start_val),
                    "end_time": minutes_to_time(end_val)
                })
            itinerary.sort(key=lambda x: x['start_time'])
            return {"itinerary": itinerary}
        else:
            return {"itinerary": []}

# Solve and print the solution
solution = solve_scheduling()
print("SOLUTION:")
print(json.dumps(solution, indent=2))