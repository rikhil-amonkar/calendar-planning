import z3
import itertools
import json

def main():
    # Define travel times
    travel_times = {
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'Fisherman\'s Wharf'): 11,
        ('Nob Hill', 'Bayview'): 19,
        ('North Beach', 'Nob Hill'): 7,
        ('North Beach', 'Fisherman\'s Wharf'): 5,
        ('North Beach', 'Bayview'): 22,
        ('Fisherman\'s Wharf', 'Nob Hill'): 11,
        ('Fisherman\'s Wharf', 'North Beach'): 6,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Bayview', 'Nob Hill'): 20,
        ('Bayview', 'North Beach'): 21,
        ('Bayview', 'Fisherman\'s Wharf'): 25,
    }

    # Friends' data
    friends = {
        'Helen': {
            'location': 'North Beach',
            'available_start': 7*60,  # 7:00 AM
            'available_end': 16*60 + 45,  # 4:45 PM
            'min_duration': 120,
        },
        'Kimberly': {
            'location': 'Fisherman\'s Wharf',
            'available_start': 16*60 + 30,  # 4:30 PM
            'available_end': 21*60,  # 9:00 PM
            'min_duration': 45,
        },
        'Patricia': {
            'location': 'Bayview',
            'available_start': 18*60,  # 6:00 PM
            'available_end': 21*60 + 15,  # 9:15 PM
            'min_duration': 120,
        },
    }

    friends_list = ['Helen', 'Kimberly', 'Patricia']

    # Try permutations in order of largest subset first
    for subset_size in range(3, 0, -1):
        for subset in itertools.combinations(friends_list, subset_size):
            for perm in itertools.permutations(subset):
                # Create variables and solver
                variables = {}
                solver = z3.Solver()
                prev_time = 540  # Start at Nob Hill at 9:00 AM (540 minutes)
                prev_location = 'Nob Hill'

                # Create variables and add constraints for each friend in the permutation
                for friend in perm:
                    location = friends[friend]['location']
                    travel_time_val = travel_times[(prev_location, location)]
                    available_start = friends[friend]['available_start']
                    available_end = friends[friend]['available_end']
                    min_duration = friends[friend]['min_duration']

                    start_var = z3.Int(friend + '_start')
                    end_var = z3.Int(friend + '_end')

                    solver.add(start_var >= prev_time + travel_time_val)
                    solver.add(start_var >= available_start)
                    solver.add(end_var >= start_var + min_duration)
                    solver.add(end_var <= available_end)

                    variables[friend] = (start_var, end_var)

                    prev_time = end_var
                    prev_location = location

                # Check if the constraints are satisfiable
                if solver.check() == z3.sat:
                    model = solver.model()
                    itinerary = []
                    for friend in perm:
                        start = model.evaluate(variables[friend][0]).as_long()
                        end = model.evaluate(variables[friend][1]).as_long()

                        # Convert to H:MM format
                        start_h = start // 60
                        start_m = start % 60
                        end_h = end // 60
                        end_m = end % 60

                        start_str = f"{start_h}:{start_m:02d}"
                        end_str = f"{end_h}:{end_m:02d}"

                        itinerary.append({
                            "action": "meet",
                            "location": friends[friend]['location'],
                            "person": friend,
                            "start_time": start_str,
                            "end_time": end_str
                        })

                    # Output the result
                    print(json.dumps({"itinerary": itinerary}))
                    return

    # If no solution found (unlikely given the problem constraints)
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()