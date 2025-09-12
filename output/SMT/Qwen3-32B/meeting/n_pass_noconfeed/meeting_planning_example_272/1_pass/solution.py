from z3 import *
import itertools
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Define friends and their constraints
    friends = [
        {
            'name': 'Timothy',
            'location': 'Embarcadero',
            'available_start': 9 * 60 + 45,  # 9:45 AM
            'available_end': 17 * 60 + 45,   # 5:45 PM
            'min_duration': 120,
        },
        {
            'name': 'Patricia',
            'location': 'Nob Hill',
            'available_start': 18 * 60 + 30,  # 6:30 PM
            'available_end': 21 * 60 + 45,   # 9:45 PM
            'min_duration': 90,
        },
        {
            'name': 'Ashley',
            'location': 'Mission District',
            'available_start': 20 * 60 + 30,  # 8:30 PM
            'available_end': 21 * 60 + 15,   # 9:15 PM
            'min_duration': 45,
        },
    ]

    # Travel times between locations
    travel_times = {
        ('Russian Hill', 'Nob Hill'): 5,
        ('Russian Hill', 'Mission District'): 16,
        ('Russian Hill', 'Embarcadero'): 8,
        ('Nob Hill', 'Russian Hill'): 5,
        ('Nob Hill', 'Mission District'): 13,
        ('Nob Hill', 'Embarcadero'): 9,
        ('Mission District', 'Russian Hill'): 15,
        ('Mission District', 'Nob Hill'): 12,
        ('Mission District', 'Embarcadero'): 19,
        ('Embarcadero', 'Russian Hill'): 8,
        ('Embarcadero', 'Nob Hill'): 10,
        ('Embarcadero', 'Mission District'): 20,
    }

    # Generate all permutations of the friends
    for perm in itertools.permutations(friends):
        solver = Solver()

        # Create variables for each friend's start time in the permutation
        starts = [Int(f'start_{i}') for i in range(len(perm))]

        prev_loc = 'Russian Hill'
        prev_end = 540  # 9:00 AM in minutes since midnight

        for i, friend in enumerate(perm):
            current_loc = friend['location']
            travel_time = travel_times[(prev_loc, current_loc)]
            arrival_time = prev_end + travel_time

            # Constraints for the start time of this friend
            solver.add(starts[i] >= arrival_time)
            solver.add(starts[i] >= friend['available_start'])
            solver.add(starts[i] + friend['min_duration'] <= friend['available_end'])

            # Update previous end time and location
            prev_end = starts[i] + friend['min_duration']
            prev_loc = current_loc

        # Check if this permutation is feasible
        if solver.check() == sat:
            model = solver.model()
            itinerary = []
            current_loc = 'Russian Hill'

            for i, friend in enumerate(perm):
                start = model.evaluate(starts[i]).as_long()
                duration = friend['min_duration']
                end = start + duration

                # Add the meeting to the itinerary
                itinerary.append({
                    'action': 'meet',
                    'location': friend['location'],
                    'person': friend['name'],
                    'start_time': minutes_to_time(start),
                    'end_time': minutes_to_time(end),
                })

                # Update current location
                current_loc = friend['location']

            # Output the result
            print(json.dumps({'itinerary': itinerary}))
            return

    # If no permutation is feasible
    print(json.dumps({'itinerary': []}))

if __name__ == '__main__':
    main()