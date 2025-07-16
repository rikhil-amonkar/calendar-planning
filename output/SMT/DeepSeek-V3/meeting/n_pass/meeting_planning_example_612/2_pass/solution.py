from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define the locations and their indices
    locations = {
        'Alamo Square': 0,
        'Russian Hill': 1,
        'Presidio': 2,
        'Chinatown': 3,
        'Sunset District': 4,
        'The Castro': 5,
        'Embarcadero': 6,
        'Golden Gate Park': 7
    }

    # Travel times matrix (minutes)
    travel_times = [
        [0, 13, 18, 16, 16, 8, 17, 9],    # Alamo Square
        [15, 0, 14, 9, 23, 21, 8, 21],    # Russian Hill
        [18, 14, 0, 21, 15, 21, 20, 12],  # Presidio
        [17, 7, 19, 0, 29, 22, 5, 23],    # Chinatown
        [17, 24, 16, 30, 0, 17, 31, 11],  # Sunset District
        [8, 18, 20, 20, 17, 0, 22, 11],   # The Castro
        [19, 8, 20, 7, 30, 25, 0, 25],    # Embarcadero
        [10, 19, 11, 23, 10, 13, 25, 0]   # Golden Gate Park
    ]

    # Friends' data: name, location, start time (minutes from midnight), end time, min duration
    friends = [
        ('Emily', 'Russian Hill', 12*60 + 15, 14*60 + 15, 105),
        ('Mark', 'Presidio', 14*60 + 45, 19*60 + 30, 60),
        ('Deborah', 'Chinatown', 7*60 + 30, 15*60 + 30, 45),
        ('Margaret', 'Sunset District', 21*60 + 30, 22*60 + 30, 60),
        ('George', 'The Castro', 7*60 + 30, 14*60 + 15, 60),
        ('Andrew', 'Embarcadero', 20*60 + 15, 22*60 + 0, 75),
        ('Steven', 'Golden Gate Park', 11*60 + 15, 21*60 + 15, 105)
    ]

    # Current location starts at Alamo Square at 9:00 AM (540 minutes)
    current_time = 9 * 60
    current_location = locations['Alamo Square']

    # Variables for each meeting: start, end, and location
    meetings = []
    for i, (name, loc, start, end, dur) in enumerate(friends):
        meet_start = Int(f'meet_start_{i}')
        meet_end = Int(f'meet_end_{i}')
        loc_idx = locations[loc]
        meetings.append((name, meet_start, meet_end, loc_idx, dur, start, end))

    # Constraints for each meeting
    for name, meet_start, meet_end, loc_idx, dur, friend_start, friend_end in meetings:
        # Meeting must start and end within friend's availability
        s.add(meet_start >= friend_start)
        s.add(meet_end <= friend_end)
        # Meeting duration must be at least the minimum
        s.add(meet_end - meet_start >= dur)
        # Meeting must start before it ends
        s.add(meet_start < meet_end)

    # Order of meetings and travel times
    # We need to define the order in which meetings occur
    # For simplicity, let's assume we can meet all friends, and let Z3 find the order
    # We'll create a list of possible orders and let Z3 choose the best one
    # This is a simplified approach; a more sophisticated method would use permutations

    # For each pair of meetings, ensure that if one comes after the other, travel time is accounted for
    for i in range(len(meetings)):
        for j in range(len(meetings)):
            if i != j:
                # Either meeting i is before j or vice versa
                # We'll let Z3 decide the order
                # To avoid circular dependencies, we'll add a constraint that ensures one is before the other
                # This is a simple way to handle ordering; a better approach would use a more sophisticated model
                s.add(Or(
                    meetings[i][2] + travel_times[meetings[i][3]][meetings[j][3]] <= meetings[j][1],
                    meetings[j][2] + travel_times[meetings[j][3]][meetings[i][3]] <= meetings[i][1]
                ))

    # Additionally, the first meeting must be after the current time plus travel time from Alamo Square
    for i in range(len(meetings)):
        s.add(meetings[i][1] >= current_time + travel_times[current_location][meetings[i][3]])

    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        schedule = []
        for i, (name, meet_start, meet_end, loc_idx, dur, friend_start, friend_end) in enumerate(meetings):
            start = m.evaluate(meet_start).as_long()
            end = m.evaluate(meet_end).as_long()
            loc = [k for k, v in locations.items() if v == loc_idx][0]
            schedule.append((name, loc, start, end))
        
        # Sort schedule by start time
        schedule.sort(key=lambda x: x[2])
        
        # Print the schedule
        print("SOLUTION:")
        for name, loc, start, end in schedule:
            start_hr = start // 60
            start_min = start % 60
            end_hr = end // 60
            end_min = end % 60
            print(f"Meet {name} at {loc} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}")
    else:
        print("No feasible schedule found.")

solve_scheduling()