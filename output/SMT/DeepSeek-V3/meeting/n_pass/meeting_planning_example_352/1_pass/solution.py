from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define the locations and their indices
    locations = {
        'Union Square': 0,
        'Nob Hill': 1,
        'Haight-Ashbury': 2,
        'Chinatown': 3,
        'Marina District': 4
    }

    # Travel times matrix (in minutes)
    travel_times = [
        [0, 9, 18, 7, 18],    # Union Square to others
        [7, 0, 13, 6, 11],     # Nob Hill to others
        [17, 15, 0, 19, 17],   # Haight-Ashbury to others
        [7, 8, 19, 0, 12],     # Chinatown to others
        [16, 12, 16, 16, 0]    # Marina District to others
    ]

    # Friends' availability and constraints
    friends = {
        'Karen': {
            'location': 'Nob Hill',
            'start': 21 * 60 + 15,  # 9:15 PM in minutes
            'end': 21 * 60 + 45,     # 9:45 PM in minutes
            'duration': 30            # minutes
        },
        'Joseph': {
            'location': 'Haight-Ashbury',
            'start': 12 * 60 + 30,    # 12:30 PM in minutes
            'end': 19 * 60 + 45,      # 7:45 PM in minutes
            'duration': 90            # minutes
        },
        'Sandra': {
            'location': 'Chinatown',
            'start': 7 * 60 + 15,    # 7:15 AM in minutes
            'end': 19 * 60 + 15,      # 7:15 PM in minutes
            'duration': 75            # minutes
        },
        'Nancy': {
            'location': 'Marina District',
            'start': 11 * 60 + 0,     # 11:00 AM in minutes
            'end': 20 * 60 + 15,      # 8:15 PM in minutes
            'duration': 105           # minutes
        }
    }

    # Current time starts at 9:00 AM (540 minutes)
    current_time = 540
    current_location = 'Union Square'

    # Variables for each friend's meeting start and end times
    meeting_vars = {}
    for friend in friends:
        meeting_vars[friend] = {
            'start': Int(f'start_{friend}'),
            'end': Int(f'end_{friend}')
        }

    # Constraints for each friend's meeting
    for friend in friends:
        data = friends[friend]
        start = meeting_vars[friend]['start']
        end = meeting_vars[friend]['end']
        s.add(start >= data['start'])
        s.add(end <= data['end'])
        s.add(end == start + data['duration'])

    # Constraints to ensure meetings do not overlap and travel times are accounted for
    friends_list = list(friends.keys())
    for i in range(len(friends_list)):
        for j in range(i + 1, len(friends_list)):
            friend1 = friends_list[i]
            friend2 = friends_list[j]
            loc1 = friends[friend1]['location']
            loc2 = friends[friend2]['location']
            travel_time = travel_times[locations[loc1]][locations[loc2]]

            # Either friend1's meeting ends before friend2's starts plus travel time, or vice versa
            s.add(Or(
                meeting_vars[friend1]['end'] + travel_time <= meeting_vars[friend2]['start'],
                meeting_vars[friend2]['end'] + travel_time <= meeting_vars[friend1]['start']
            ))

    # Constraint to ensure the first meeting starts after travel from Union Square
    for friend in friends:
        loc = friends[friend]['location']
        travel_time = travel_times[locations[current_location]][locations[loc]]
        s.add(meeting_vars[friend]['start'] >= current_time + travel_time)

    # Try to meet as many friends as possible (all in this case)
    # Check if all meetings can be scheduled
    if s.check() == sat:
        model = s.model()
        schedule = []
        for friend in friends:
            start = model[meeting_vars[friend]['start']].as_long()
            end = model[meeting_vars[friend]['end']].as_long()
            schedule.append({
                'friend': friend,
                'location': friends[friend]['location'],
                'start': f"{start // 60}:{start % 60:02d}",
                'end': f"{end // 60}:{end % 60:02d}"
            })
        # Sort schedule by start time
        schedule.sort(key=lambda x: int(x['start'].split(':')[0]) * 60 + int(x['start'].split(':')[1]))
        return schedule
    else:
        return None

schedule = solve_scheduling()
if schedule:
    print("SOLUTION:")
    for meeting in schedule:
        print(f"Meet {meeting['friend']} at {meeting['location']} from {meeting['start']} to {meeting['end']}")
else:
    print("No valid schedule found.")