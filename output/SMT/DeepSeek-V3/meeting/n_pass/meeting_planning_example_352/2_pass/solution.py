from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define locations and their indices
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

    # Friends' data
    friends = [
        {
            'name': 'Karen',
            'location': 'Nob Hill',
            'available_start': 21 * 60 + 15,  # 9:15 PM in minutes
            'available_end': 21 * 60 + 45,    # 9:45 PM in minutes
            'duration': 30                    # minutes
        },
        {
            'name': 'Joseph',
            'location': 'Haight-Ashbury',
            'available_start': 12 * 60 + 30,  # 12:30 PM in minutes
            'available_end': 19 * 60 + 45,    # 7:45 PM in minutes
            'duration': 90                     # minutes
        },
        {
            'name': 'Sandra',
            'location': 'Chinatown',
            'available_start': 7 * 60 + 15,    # 7:15 AM in minutes
            'available_end': 19 * 60 + 15,     # 7:15 PM in minutes
            'duration': 75                     # minutes
        },
        {
            'name': 'Nancy',
            'location': 'Marina District',
            'available_start': 11 * 60 + 0,    # 11:00 AM in minutes
            'available_end': 20 * 60 + 15,     # 8:15 PM in minutes
            'duration': 105                    # minutes
        }
    ]

    # Create variables for each meeting
    meeting_starts = [Int(f'start_{f["name"]}') for f in friends]
    meeting_ends = [Int(f'end_{f["name"]}') for f in friends]

    # Current time starts at 9:00 AM (540 minutes)
    current_time = 540
    current_location = 'Union Square'

    # Add constraints for each friend
    for i, friend in enumerate(friends):
        # Meeting must be within friend's availability
        s.add(meeting_starts[i] >= friend['available_start'])
        s.add(meeting_ends[i] <= friend['available_end'])
        # Meeting duration must be exactly as specified
        s.add(meeting_ends[i] == meeting_starts[i] + friend['duration'])
        # First meeting must account for travel from Union Square
        travel_time = travel_times[locations[current_location]][locations[friend['location']]]
        s.add(meeting_starts[i] >= current_time + travel_time)

    # Add constraints to prevent overlapping meetings with travel time
    for i in range(len(friends)):
        for j in range(i + 1, len(friends)):
            # Travel time between locations
            loc_i = locations[friends[i]['location']]
            loc_j = locations[friends[j]['location']]
            travel_ij = travel_times[loc_i][loc_j]
            travel_ji = travel_times[loc_j][loc_i]

            # Either meeting i is before meeting j with travel time
            # Or meeting j is before meeting i with travel time
            s.add(Or(
                meeting_ends[i] + travel_ij <= meeting_starts[j],
                meeting_ends[j] + travel_ji <= meeting_starts[i]
            ))

    # Try to schedule all meetings
    if s.check() == sat:
        model = s.model()
        schedule = []
        for i, friend in enumerate(friends):
            start = model[meeting_starts[i]].as_long()
            end = model[meeting_ends[i]].as_long()
            schedule.append({
                'friend': friend['name'],
                'location': friend['location'],
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
    print("No valid schedule found that meets all constraints.")