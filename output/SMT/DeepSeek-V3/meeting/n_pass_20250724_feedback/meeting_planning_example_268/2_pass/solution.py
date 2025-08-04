from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Travel times dictionary: (from, to) -> minutes
    travel_times = {
        ('Golden Gate Park', 'Alamo Square'): 10,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Golden Gate Park', 'Russian Hill'): 19,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Alamo Square', 'Presidio'): 18,
        ('Alamo Square', 'Russian Hill'): 13,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Alamo Square'): 18,
        ('Presidio', 'Russian Hill'): 14,
        ('Russian Hill', 'Golden Gate Park'): 21,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'Presidio'): 14,
    }

    # Friend data: name -> (location, start_availability, end_availability, min_duration)
    friends = {
        'Timothy': ('Alamo Square', '12:00', '16:15', 105),
        'Mark': ('Presidio', '18:45', '21:00', 60),
        'Joseph': ('Russian Hill', '16:45', '21:30', 60)
    }

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Initialize variables for each friend's meeting start and end times
    meeting_vars = {}
    for name in friends:
        start_var = Int(f'start_{name}')
        end_var = Int(f'end_{name}')
        meeting_vars[name] = (start_var, end_var)

    # Current location starts at Golden Gate Park at 9:00 AM (540 minutes)
    current_location = 'Golden Gate Park'
    current_time = 540  # 9:00 AM in minutes

    # Assume the order is Timothy, Joseph, Mark
    friend_order = ['Timothy', 'Joseph', 'Mark']

    # Add constraints for each friend in the order
    prev_end_time = current_time
    prev_location = current_location

    for name in friend_order:
        location, start_avail, end_avail, min_duration = friends[name]
        start_var, end_var = meeting_vars[name]

        # Meeting must start and end within friend's availability
        start_avail_min = time_to_minutes(start_avail)
        end_avail_min = time_to_minutes(end_avail)
        s.add(start_var >= start_avail_min)
        s.add(end_var <= end_avail_min)

        # Meeting duration must be at least min_duration
        s.add(end_var - start_var >= min_duration)

        # Travel time from previous location to current friend's location
        travel_time = travel_times[(prev_location, location)]
        s.add(start_var >= prev_end_time + travel_time)

        # Update previous end time and location
        prev_end_time = end_var
        prev_location = location

    # Check if all constraints can be satisfied
    if s.check() == sat:
        model = s.model()
        # Extract the meeting times from the model
        result_itinerary = []
        for name in friend_order:
            start_var, end_var = meeting_vars[name]
            start_time = model.evaluate(start_var).as_long()
            end_time = model.evaluate(end_var).as_long()
            result_itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start_time),
                "end_time": minutes_to_time(end_time)
            })
        return {"itinerary": result_itinerary}
    else:
        return {"itinerary": []}

# Run the solver
solution = solve_scheduling()
print(solution)