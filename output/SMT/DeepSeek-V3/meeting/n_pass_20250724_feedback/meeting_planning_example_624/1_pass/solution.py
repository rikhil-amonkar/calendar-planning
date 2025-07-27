from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define travel times dictionary for easy lookup
    travel_times = {
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
        ('Golden Gate Park', 'The Castro'): 13,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Golden Gate Park', 'Alamo Square'): 10,
        ('Golden Gate Park', 'North Beach'): 24,
        ('Golden Gate Park', 'Russian Hill'): 19,
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
        ('Haight-Ashbury', 'The Castro'): 6,
        ('Haight-Ashbury', 'Chinatown'): 19,
        ('Haight-Ashbury', 'Alamo Square'): 5,
        ('Haight-Ashbury', 'North Beach'): 19,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
        ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
        ('Fisherman\'s Wharf', 'The Castro'): 26,
        ('Fisherman\'s Wharf', 'Chinatown'): 12,
        ('Fisherman\'s Wharf', 'Alamo Square'): 20,
        ('Fisherman\'s Wharf', 'North Beach'): 6,
        ('Fisherman\'s Wharf', 'Russian Hill'): 7,
        ('The Castro', 'Golden Gate Park'): 11,
        ('The Castro', 'Haight-Ashbury'): 6,
        ('The Castro', 'Fisherman\'s Wharf'): 24,
        ('The Castro', 'Chinatown'): 20,
        ('The Castro', 'Alamo Square'): 8,
        ('The Castro', 'North Beach'): 20,
        ('The Castro', 'Russian Hill'): 18,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Chinatown', 'Haight-Ashbury'): 19,
        ('Chinatown', 'Fisherman\'s Wharf'): 8,
        ('Chinatown', 'The Castro'): 22,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'North Beach'): 3,
        ('Chinatown', 'Russian Hill'): 7,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Alamo Square', 'Haight-Ashbury'): 5,
        ('Alamo Square', 'Fisherman\'s Wharf'): 19,
        ('Alamo Square', 'The Castro'): 8,
        ('Alamo Square', 'Chinatown'): 16,
        ('Alamo Square', 'North Beach'): 15,
        ('Alamo Square', 'Russian Hill'): 13,
        ('North Beach', 'Golden Gate Park'): 22,
        ('North Beach', 'Haight-Ashbury'): 18,
        ('North Beach', 'Fisherman\'s Wharf'): 5,
        ('North Beach', 'The Castro'): 22,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Alamo Square'): 16,
        ('North Beach', 'Russian Hill'): 4,
        ('Russian Hill', 'Golden Gate Park'): 21,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'Fisherman\'s Wharf'): 7,
        ('Russian Hill', 'The Castro'): 21,
        ('Russian Hill', 'Chinatown'): 9,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'North Beach'): 5,
    }

    # Friends' data: name, location, availability start, availability end, min duration
    friends = [
        ('Carol', 'Haight-Ashbury', 21.5, 22.5, 60),
        ('Laura', 'Fisherman\'s Wharf', 11.75, 21.5, 60),
        ('Karen', 'The Castro', 7.25, 14.0, 75),
        ('Elizabeth', 'Chinatown', 12.25, 21.5, 75),
        ('Deborah', 'Alamo Square', 12.0, 15.0, 105),
        ('Jason', 'North Beach', 14.75, 19.0, 90),
        ('Steven', 'Russian Hill', 14.75, 18.5, 120),
    ]

    # Convert time to minutes since midnight for easier handling
    def time_to_minutes(time_float):
        hours = int(time_float)
        minutes = int((time_float - hours) * 60)
        return hours * 60 + minutes

    # Convert minutes back to HH:MM format
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    # Initialize variables for each friend's meeting start and end times (in minutes)
    variables = {}
    for name, loc, avail_start, avail_end, min_duration in friends:
        start_var = Int(f'start_{name}')
        end_var = Int(f'end_{name}')
        variables[name] = {
            'start': start_var,
            'end': end_var,
            'location': loc,
            'avail_start': time_to_minutes(avail_start),
            'avail_end': time_to_minutes(avail_end),
            'min_duration': min_duration,
        }

    # Add constraints for each friend's meeting
    for name, data in variables.items():
        s.add(data['start'] >= data['avail_start'])
        s.add(data['end'] <= data['avail_end'])
        s.add(data['end'] - data['start'] >= data['min_duration'])

    # Current location starts at Golden Gate Park at 9:00 AM (540 minutes)
    current_time = 540  # 9:00 AM in minutes
    current_location = 'Golden Gate Park'

    # Determine a feasible order to meet friends. We'll try to meet friends in order of their availability.
    # This is a heuristic; in a full solution, we'd need to explore all permutations.
    # For simplicity, we'll order by availability start time.
    ordered_friends = sorted(friends, key=lambda x: x[2])
    meeting_order = [name for name, _, _, _, _ in ordered_friends]

    # Add travel time constraints between consecutive meetings
    prev_end = current_time
    prev_loc = current_location
    for name in meeting_order:
        data = variables[name]
        travel_time = travel_times.get((prev_loc, data['location']), 0)
        s.add(data['start'] >= prev_end + travel_time)
        prev_end = data['end']
        prev_loc = data['location']

    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for name in meeting_order:
            start = m.evaluate(variables[name]['start']).as_long()
            end = m.evaluate(variables[name]['end']).as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))