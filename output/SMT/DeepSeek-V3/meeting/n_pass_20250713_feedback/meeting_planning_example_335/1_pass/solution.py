from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define the locations and their indices
    locations = {
        'Pacific Heights': 0,
        'North Beach': 1,
        'Financial District': 2,
        'Alamo Square': 3,
        'Mission District': 4
    }

    # Travel times matrix (in minutes)
    travel_times = [
        [0, 9, 13, 10, 15],    # Pacific Heights to others
        [8, 0, 8, 16, 18],     # North Beach to others
        [13, 7, 0, 17, 17],    # Financial District to others
        [10, 15, 17, 0, 10],   # Alamo Square to others
        [16, 17, 17, 11, 0]     # Mission District to others
    ]

    # Define the friends and their constraints
    friends = [
        {'name': 'Helen', 'location': 'North Beach', 'start': 9*60, 'end': 17*60, 'duration': 15},
        {'name': 'Betty', 'location': 'Financial District', 'start': 19*60, 'end': 21*60 + 45, 'duration': 90},
        {'name': 'Amanda', 'location': 'Alamo Square', 'start': 19*60 + 45, 'end': 21*60, 'duration': 60},
        {'name': 'Kevin', 'location': 'Mission District', 'start': 10*60 + 45, 'end': 14*60 + 45, 'duration': 45}
    ]

    # Create variables for each friend's meeting start and end times
    meet_start = [Int(f'meet_start_{i}') for i in range(len(friends))]
    meet_end = [Int(f'meet_end_{i}') for i in range(len(friends))]
    meet_loc = [locations[f['location']] for f in friends]

    # Current location starts at Pacific Heights (index 0)
    current_loc = 0
    current_time = 9 * 60  # 9:00 AM in minutes

    # Constraints for each friend
    for i in range(len(friends)):
        friend = friends[i]
        # Meeting must start and end within friend's availability
        s.add(meet_start[i] >= friend['start'])
        s.add(meet_end[i] <= friend['end'])
        # Meeting duration must be at least the required duration
        s.add(meet_end[i] - meet_start[i] >= friend['duration'])
        # Travel time to the friend's location
        if i == 0:
            # First meeting: travel from current_loc to friend's location
            s.add(meet_start[i] >= current_time + travel_times[current_loc][meet_loc[i]])
        else:
            # Subsequent meetings: travel from previous location to current friend's location
            s.add(meet_start[i] >= meet_end[i-1] + travel_times[meet_loc[i-1]][meet_loc[i]])

    # No overlapping meetings (implicitly handled by sequential travel constraints)

    # Maximize the number of friends met (all meetings must be scheduled)
    # We can also add a soft constraint to minimize total time, but here we just ensure all meetings are scheduled
    # To prioritize certain friends, we can adjust the order or add weights

    # Check if all constraints can be satisfied
    if s.check() == sat:
        m = s.model()
        # Extract the meeting times
        schedule = []
        for i in range(len(friends)):
            start = m[meet_start[i]].as_long()
            end = m[meet_end[i]].as_long()
            schedule.append({
                'name': friends[i]['name'],
                'location': friends[i]['location'],
                'start': f"{start // 60}:{start % 60:02d}",
                'end': f"{end // 60}:{end % 60:02d}",
                'duration': end - start
            })
        # Print the schedule
        print("SOLUTION:")
        for meeting in schedule:
            print(f"Meet {meeting['name']} at {meeting['location']} from {meeting['start']} to {meeting['end']} (duration: {meeting['duration']} minutes)")
    else:
        print("No valid schedule found.")

solve_scheduling()