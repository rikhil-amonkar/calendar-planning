from z3 import Solver, Int, sat, IntVal

def check_permutation(perm, travel_times):
    solver = Solver()
    start_vars = {}
    end_vars = {}

    prev_end = 540  # start at Union Square at 9:00 AM (540 mins)
    prev_loc = 'Union Square'

    for friend in perm:
        name = friend['name']
        loc = friend['location']
        avail_start = friend['available_start']
        avail_end = friend['available_end']
        min_dur = friend['min_duration']

        # Safely access travel time to prevent KeyError
        try:
            travel_time = travel_times[(prev_loc, loc)]
        except KeyError:
            raise ValueError(f"No travel time defined between {prev_loc} and {loc}")

        # Arrival time at current location
        arrival_time = prev_end + travel_time

        # Define start and end variables for this friend
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')

        # Add constraints for start time
        solver.add(start >= arrival_time)
        solver.add(start >= avail_start)

        # Add constraint for end time: at least start + min_duration
        solver.add(end >= start + min_dur)
        solver.add(end <= avail_end)

        # Store variables
        start_vars[name] = start
        end_vars[name] = end

        # Update for next iteration
        prev_end = end
        prev_loc = loc

    # Check if a solution exists
    if solver.check() == sat:
        model = solver.model()
        times = []
        for friend in perm:
            name = friend['name']
            start_val = model[start_vars[name]].as_long()
            end_val = model[end_vars[name]].as_long()
            times.append((name, start_val, end_val))
        return True, times
    else:
        return False, None