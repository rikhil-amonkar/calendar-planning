import itertools
from z3 import *
import json

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

        # Compute travel time from previous location to current location
        travel_time = travel_times[(prev_loc, loc)]

        # Arrival time at current location is prev_end + travel_time
        arrival_time = prev_end + travel_time

        # Define start variable for this friend
        start = Int(f'start_{name}')
        # Add constraints for start time
        solver.add(start >= arrival_time)
        solver.add(start >= avail_start)

        # End time is start + min_duration
        end = start + min_dur
        # Add constraint for end time
        solver.add(end <= avail_end)

        # Store variables
        start_vars[name] = start
        end_vars[name] = end

        # Update prev_end and prev_loc for next iteration
        prev_end = end
        prev_loc = loc

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

def main():
    friends = [
        {
            'name': 'Carol',
            'location': 'Sunset District',
            'available_start': 615,  # 10:15 AM
            'available_end': 645,    # 11:45 AM
            'min_duration': 30
        },
        {
            'name': 'Rebecca',
            'location': 'Mission District',
            'available_start': 690,  # 11:30 AM
            'available_end': 975,    # 8:15 PM
            'min_duration': 120
        },
        {
            'name': 'Karen',
            'location': 'Bayview',
            'available_start': 765,  # 12:45 PM
            'available_end': 900,    # 3:00 PM
            'min_duration': 120
        }
    ]

    travel_times = {
        ('Union Square', 'Mission District'): 14,
        ('Union Square', 'Bayview'): 15,
        ('Union Square', 'Sunset District'): 26,
        ('Mission District', 'Union Square'): 15,
        ('Mission District', 'Bayview'): 15,
        ('Mission District', 'Sunset District'): 24,
        ('Bayview', 'Union Square'): 17,
        ('Bayview', 'Mission District'): 13,
        ('Bayview', 'Sunset District'): 23,
        ('Sunset District', 'Union Square'): 30,
        ('Sunset District', 'Mission District'): 24,
        ('Sunset District', 'Bayview'): 22,
    }

    for size in range(3, 0, -1):
        for combo in itertools.combinations(friends, size):
            for perm in itertools.permutations(combo):
                feasible, times = check_permutation(perm, travel_times)
                if feasible:
                    itinerary = []
                    for name, start, end in times:
                        def to_time_str(m):
                            hours = m // 60
                            minutes = m % 60
                            return f"{hours}:{minutes:02d}"
                        location = next(f['location'] for f in friends if f['name'] == name)
                        itinerary.append({
                            "action": "meet",
                            "location": location,
                            "person": name,
                            "start_time": to_time_str(start),
                            "end_time": to_time_str(end)
                        })
                    print(json.dumps({"itinerary": itinerary}, indent=2))
                    return

    # If no solution found for any size, output empty itinerary?
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()