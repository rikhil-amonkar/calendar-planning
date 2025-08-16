import itertools
from z3 import *

def main():
    # Define the travel times between locations
    travel_time = {
        ('Bayview', 'North Beach'): 21,
        ('Bayview', 'Presidio'): 31,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'Union Square'): 17,
        ('North Beach', 'Bayview'): 22,
        ('North Beach', 'Presidio'): 17,
        ('North Beach', 'Haight-Ashbury'): 18,
        ('North Beach', 'Union Square'): 7,
        ('Presidio', 'Bayview'): 31,
        ('Presidio', 'North Beach'): 18,
        ('Presidio', 'Haight-Ashbury'): 15,
        ('Presidio', 'Union Square'): 22,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Haight-Ashbury', 'North Beach'): 19,
        ('Haight-Ashbury', 'Presidio'): 15,
        ('Haight-Ashbury', 'Union Square'): 17,
        ('Union Square', 'Bayview'): 15,
        ('Union Square', 'North Beach'): 10,
        ('Union Square', 'Presidio'): 24,
        ('Union Square', 'Haight-Ashbury'): 18,
    }

    friends = [
        {'name': 'Barbara', 'location': 'North Beach', 'available_start': 825, 'available_end': 1215, 'duration': 60},
        {'name': 'Margaret', 'location': 'Presidio', 'available_start': 615, 'available_end': 915, 'duration': 30},
        {'name': 'Kevin', 'location': 'Haight-Ashbury', 'available_start': 1200, 'available_end': 1245, 'duration': 30},
        {'name': 'Kimberly', 'location': 'Union Square', 'available_start': 465, 'available_end': 1005, 'duration': 30},
    ]

    from itertools import permutations

    for perm in permutations(friends):
        solver = Solver()
        previous_end_time = 540  # 9:00 AM in minutes
        previous_location = 'Bayview'
        start_vars = {}

        for friend in perm:
            current_location = friend['location']
            travel_time_val = travel_time[(previous_location, current_location)]
            arrival_time = previous_end_time + travel_time_val
            var_name = f"{friend['name']}_start"
            s = Int(var_name)
            solver.add(s >= arrival_time)
            solver.add(s >= friend['available_start'])
            solver.add(s + friend['duration'] <= friend['available_end'])
            start_vars[friend['name']] = s
            previous_end_time = s + friend['duration']
            previous_location = current_location

        if solver.check() == sat:
            model = solver.model()
            itinerary = []
            for friend in perm:
                s = start_vars[friend['name']]
                start_val = model.evaluate(s).as_long()
                end_val = start_val + friend['duration']
                # Convert to HH:MM
                start_h = start_val // 60
                start_m = start_val % 60
                end_h = end_val // 60
                end_m = end_val % 60
                start_time = f"{start_h:02d}:{start_m:02d}"
                end_time = f"{end_h:02d}:{end_m:02d}"
                itinerary.append({"action": "meet", "person": friend['name'], "start_time": start_time, "end_time": end_time})
            # Output the solution
            print("SOLUTION:")
            print(json.dumps({"itinerary": itinerary}))
            return

if __name__ == "__main__":
    main()