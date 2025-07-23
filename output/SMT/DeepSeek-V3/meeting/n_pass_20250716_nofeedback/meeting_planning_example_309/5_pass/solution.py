from z3 import *
import datetime

def solve_scheduling_problem():
    # Initialize Z3 optimizer
    opt = Optimize()

    # Define locations and travel times (in minutes)
    locations = {
        'Financial District': 0,
        'Chinatown': 1,
        'Alamo Square': 2,
        'Bayview': 3,
        'Fisherman\'s Wharf': 4
    }

    travel_times = [
        [0, 5, 17, 19, 10],    # Financial District to others
        [5, 0, 17, 22, 8],     # Chinatown to others
        [17, 16, 0, 16, 19],   # Alamo Square to others
        [19, 18, 16, 0, 25],    # Bayview to others
        [11, 12, 20, 26, 0]     # Fisherman's Wharf to others
    ]

    # Friends' availability and constraints
    friends = {
        'Nancy': {
            'location': 'Chinatown',
            'start': datetime.time(9, 30),
            'end': datetime.time(13, 30),
            'duration': 90  # minutes
        },
        'Mary': {
            'location': 'Alamo Square',
            'start': datetime.time(7, 0),
            'end': datetime.time(21, 0),
            'duration': 75  # minutes
        },
        'Jessica': {
            'location': 'Bayview',
            'start': datetime.time(11, 15),
            'end': datetime.time(13, 45),
            'duration': 45  # minutes
        },
        'Rebecca': {
            'location': 'Fisherman\'s Wharf',
            'start': datetime.time(7, 0),
            'end': datetime.time(8, 30),
            'duration': 45  # minutes
        }
    }

    # Current time starts at 9:00 AM in Financial District
    current_time = datetime.datetime.combine(datetime.date.today(), datetime.time(9, 0))
    current_location = 'Financial District'

    # Variables to track meetings
    meetings = []
    meet_vars = []  # To track which meetings are scheduled

    # For each friend, create variables
    for friend, details in friends.items():
        start_var = Int(f'start_{friend}')
        end_var = Int(f'end_{friend}')
        duration_var = details['duration']
        meet_var = Bool(f'meet_{friend}')  # Whether we meet this friend

        # Convert friend's availability to minutes since 9:00 AM
        friend_start = (details['start'].hour - 9) * 60 + details['start'].minute
        friend_end = (details['end'].hour - 9) * 60 + details['end'].minute

        # Constraints if we meet this friend
        opt.add(Implies(meet_var, start_var >= max(friend_start, 0)))  # Can't start before 9:00
        opt.add(Implies(meet_var, end_var <= friend_end))
        opt.add(Implies(meet_var, end_var == start_var + duration_var))

        meetings.append({
            'friend': friend,
            'start_var': start_var,
            'end_var': end_var,
            'meet_var': meet_var,
            'location': details['location'],
            'duration': duration_var
        })
        meet_vars.append(meet_var)

    # Add constraints for meeting sequence and travel times
    for i in range(len(meetings)):
        for j in range(i + 1, len(meetings)):
            m1 = meetings[i]
            m2 = meetings[j]

            # Travel time between locations
            travel_time = travel_times[locations[m1['location']]][locations[m2['location']]]

            # If both meetings happen, they must not overlap with travel time
            opt.add(Implies(And(m1['meet_var'], m2['meet_var']),
                    Or(
                        m1['end_var'] + travel_time <= m2['start_var'],
                        m2['end_var'] + travel_time <= m1['start_var']
                    )))

    # First meeting must be after travel from Financial District
    for meeting in meetings:
        travel_time = travel_times[locations[current_location]][locations[meeting['location']]]
        opt.add(Implies(meeting['meet_var'], meeting['start_var'] >= travel_time))

    # Special case for Rebecca (early morning meeting)
    # Since we start at 9:00 AM, we can't meet Rebecca (7:00-8:30 AM)
    rebecca_meet = [m['meet_var'] for m in meetings if m['friend'] == 'Rebecca'][0]
    opt.add(Not(rebecca_meet))

    # Maximize number of meetings first, then total meeting time
    num_meetings = Sum([If(var, 1, 0) for var in meet_vars])
    total_time = Sum([If(m['meet_var'], m['duration'], 0) for m in meetings])
    opt.maximize(num_meetings)
    opt.maximize(total_time)

    # Check if a solution exists
    if opt.check() == sat:
        model = opt.model()
        scheduled_meetings = []
        for meeting in meetings:
            if model[meeting['meet_var']]:
                start_min = model[meeting['start_var']].as_long()
                end_min = start_min + meeting['duration']
                start_time = (datetime.datetime.combine(datetime.date.today(), datetime.time(9, 0)) + 
                             datetime.timedelta(minutes=start_min)).time()
                end_time = (datetime.datetime.combine(datetime.date.today(), datetime.time(9, 0)) + 
                           datetime.timedelta(minutes=end_min)).time()
                scheduled_meetings.append({
                    'action': 'meet',
                    'person': meeting['friend'],
                    'start_time': start_time.strftime('%H:%M'),
                    'end_time': end_time.strftime('%H:%M')
                })
        
        # Sort meetings by start time
        scheduled_meetings.sort(key=lambda x: x['start_time'])
        return {'itinerary': scheduled_meetings}
    else:
        return {'itinerary': []}

# Run the optimizer
result = solve_scheduling_problem()
print(result)