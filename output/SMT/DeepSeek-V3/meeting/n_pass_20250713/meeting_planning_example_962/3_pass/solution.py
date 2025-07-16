from z3 import *
from itertools import combinations

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define the locations and their travel times
    travel_times = {
        'The Castro': {
            'Marina District': 21,
            'Presidio': 20,
            'North Beach': 20,
            'Embarcadero': 22,
            'Haight-Ashbury': 6,
            'Golden Gate Park': 11,
            'Richmond District': 16,
            'Alamo Square': 8,
            'Financial District': 21,
            'Sunset District': 17
        },
        'Marina District': {
            'The Castro': 22,
            'Presidio': 10,
            'North Beach': 11,
            'Embarcadero': 14,
            'Haight-Ashbury': 16,
            'Golden Gate Park': 18,
            'Richmond District': 11,
            'Alamo Square': 15,
            'Financial District': 17,
            'Sunset District': 19
        },
        'Presidio': {
            'The Castro': 21,
            'Marina District': 11,
            'North Beach': 18,
            'Embarcadero': 20,
            'Haight-Ashbury': 15,
            'Golden Gate Park': 12,
            'Richmond District': 7,
            'Alamo Square': 19,
            'Financial District': 23,
            'Sunset District': 15
        },
        'North Beach': {
            'The Castro': 23,
            'Marina District': 9,
            'Presidio': 17,
            'Embarcadero': 6,
            'Haight-Ashbury': 18,
            'Golden Gate Park': 22,
            'Richmond District': 18,
            'Alamo Square': 16,
            'Financial District': 8,
            'Sunset District': 27
        },
        'Embarcadero': {
            'The Castro': 25,
            'Marina District': 12,
            'Presidio': 20,
            'North Beach': 5,
            'Haight-Ashbury': 21,
            'Golden Gate Park': 25,
            'Richmond District': 21,
            'Alamo Square': 19,
            'Financial District': 5,
            'Sunset District': 30
        },
        'Haight-Ashbury': {
            'The Castro': 6,
            'Marina District': 17,
            'Presidio': 15,
            'North Beach': 19,
            'Embarcadero': 20,
            'Golden Gate Park': 7,
            'Richmond District': 10,
            'Alamo Square': 5,
            'Financial District': 21,
            'Sunset District': 15
        },
        'Golden Gate Park': {
            'The Castro': 13,
            'Marina District': 16,
            'Presidio': 11,
            'North Beach': 23,
            'Embarcadero': 25,
            'Haight-Ashbury': 7,
            'Richmond District': 7,
            'Alamo Square': 9,
            'Financial District': 26,
            'Sunset District': 10
        },
        'Richmond District': {
            'The Castro': 16,
            'Marina District': 9,
            'Presidio': 7,
            'North Beach': 17,
            'Embarcadero': 19,
            'Haight-Ashbury': 10,
            'Golden Gate Park': 9,
            'Alamo Square': 13,
            'Financial District': 22,
            'Sunset District': 11
        },
        'Alamo Square': {
            'The Castro': 8,
            'Marina District': 15,
            'Presidio': 17,
            'North Beach': 15,
            'Embarcadero': 16,
            'Haight-Ashbury': 5,
            'Golden Gate Park': 9,
            'Richmond District': 11,
            'Financial District': 17,
            'Sunset District': 16
        },
        'Financial District': {
            'The Castro': 20,
            'Marina District': 15,
            'Presidio': 22,
            'North Beach': 7,
            'Embarcadero': 4,
            'Haight-Ashbury': 19,
            'Golden Gate Park': 23,
            'Richmond District': 21,
            'Alamo Square': 17,
            'Sunset District': 30
        },
        'Sunset District': {
            'The Castro': 17,
            'Marina District': 21,
            'Presidio': 16,
            'North Beach': 28,
            'Embarcadero': 30,
            'Haight-Ashbury': 15,
            'Golden Gate Park': 11,
            'Richmond District': 12,
            'Alamo Square': 17,
            'Financial District': 30
        }
    }

    # Define the friends and their constraints
    friends = [
        {'name': 'Elizabeth', 'location': 'Marina District', 'start': 19*60, 'end': 20*60 + 45, 'min_duration': 105},
        {'name': 'Joshua', 'location': 'Presidio', 'start': 8*60 + 30, 'end': 13*60 + 15, 'min_duration': 105},
        {'name': 'Timothy', 'location': 'North Beach', 'start': 19*60 + 45, 'end': 22*60, 'min_duration': 90},
        {'name': 'David', 'location': 'Embarcadero', 'start': 10*60 + 45, 'end': 12*60 + 30, 'min_duration': 30},
        {'name': 'Kimberly', 'location': 'Haight-Ashbury', 'start': 16*60 + 45, 'end': 21*60 + 30, 'min_duration': 75},
        {'name': 'Lisa', 'location': 'Golden Gate Park', 'start': 17*60 + 30, 'end': 21*60 + 45, 'min_duration': 45},
        {'name': 'Ronald', 'location': 'Richmond District', 'start': 8*60, 'end': 9*60 + 30, 'min_duration': 90},
        {'name': 'Stephanie', 'location': 'Alamo Square', 'start': 15*60 + 30, 'end': 16*60 + 30, 'min_duration': 30},
        {'name': 'Helen', 'location': 'Financial District', 'start': 17*60 + 30, 'end': 18*60 + 30, 'min_duration': 45},
        {'name': 'Laura', 'location': 'Sunset District', 'start': 17*60 + 45, 'end': 21*60 + 15, 'min_duration': 90}
    ]

    # Generate all possible combinations of 6 friends
    for selected_friends in combinations(friends, 6):
        s = Solver()

        # Create variables for each selected friend's meeting start and end times
        meeting_starts = {}
        meeting_ends = {}
        for friend in selected_friends:
            name = friend['name']
            meeting_starts[name] = Int(f'start_{name}')
            meeting_ends[name] = Int(f'end_{name}')

        # Current location starts at The Castro at 9:00 AM (540 minutes)
        current_time = 540
        current_location = 'The Castro'

        # Constraints for each selected friend
        for friend in selected_friends:
            name = friend['name']
            location = friend['location']
            start_window = friend['start']
            end_window = friend['end']
            min_duration = friend['min_duration']

            # Meeting must be within the friend's availability window
            s.add(meeting_starts[name] >= start_window)
            s.add(meeting_ends[name] <= end_window)
            s.add(meeting_ends[name] >= meeting_starts[name] + min_duration)

            # Travel time from current location to friend's location
            travel_time = travel_times[current_location][location]
            s.add(meeting_starts[name] >= current_time + travel_time)

            # Update current_time and current_location after meeting
            current_time = meeting_ends[name]
            current_location = location

        # Check if the current combination is feasible
        if s.check() == sat:
            m = s.model()
            schedule = []
            for friend in selected_friends:
                name = friend['name']
                start = m[meeting_starts[name]].as_long()
                end = m[meeting_ends[name]].as_long()
                duration = end - start
                schedule.append({
                    'name': name,
                    'location': friend['location'],
                    'start': f"{start // 60}:{start % 60:02d}",
                    'end': f"{end // 60}:{end % 60:02d}",
                    'duration': duration
                })
            return schedule

    return None

schedule = solve_scheduling()
if schedule:
    print("SOLUTION:")
    for meeting in schedule:
        print(f"Meet {meeting['name']} at {meeting['location']} from {meeting['start']} to {meeting['end']} (duration: {meeting['duration']} minutes)")
else:
    print("No valid schedule found.")