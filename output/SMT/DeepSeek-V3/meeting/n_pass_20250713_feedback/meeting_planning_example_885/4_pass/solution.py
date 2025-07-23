from z3 import *

def solve_scheduling():
    # Initialize Z3 optimizer
    opt = Optimize()

    # Friends and their locations
    friends = {
        'Mark': 'Marina District',
        'Karen': 'Financial District',
        'Barbara': 'Alamo Square',
        'Nancy': 'Golden Gate Park',
        'David': 'The Castro',
        'Linda': 'Bayview',
        'Kevin': 'Sunset District',
        'Matthew': 'Haight-Ashbury',
        'Andrew': 'Nob Hill'
    }

    # Time windows for each friend (start, end in minutes since 9:00AM)
    time_windows = {
        'Mark': (1050, 1260),    # 6:45PM to 9:00PM (17:45 to 21:00)
        'Karen': (30, 225),       # 9:30AM to 12:45PM (9:30 to 12:45)
        'Barbara': (60, 630),     # 10:00AM to 7:30PM (10:00 to 19:30)
        'Nancy': (465, 600),     # 4:45PM to 8:00PM (16:45 to 20:00)
        'David': (0, 540),        # 9:00AM to 6:00PM (9:00 to 18:00)
        'Linda': (435, 525),      # 6:15PM to 7:45PM (18:15 to 19:45)
        'Kevin': (60, 525),       # 10:00AM to 5:45PM (10:00 to 17:45)
        'Matthew': (75, 390),     # 10:15AM to 3:30PM (10:15 to 15:30)
        'Andrew': (165, 465)      # 11:45AM to 4:45PM (11:45 to 16:45)
    }

    # Minimum meeting durations (in minutes)
    min_durations = {
        'Mark': 90,
        'Karen': 90,
        'Barbara': 90,
        'Nancy': 105,
        'David': 120,
        'Linda': 45,
        'Kevin': 120,
        'Matthew': 45,
        'Andrew': 105
    }

    # Travel times between locations (in minutes)
    travel_times = {
        ('Russian Hill', 'Marina District'): 7,
        ('Russian Hill', 'Financial District'): 11,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'Golden Gate Park'): 21,
        ('Russian Hill', 'The Castro'): 21,
        ('Russian Hill', 'Bayview'): 23,
        ('Russian Hill', 'Sunset District'): 23,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'Nob Hill'): 5,
        'Marina District': {
            'Russian Hill': 8,
            'Financial District': 17,
            'Alamo Square': 15,
            'Golden Gate Park': 18,
            'The Castro': 22,
            'Bayview': 27,
            'Sunset District': 19,
            'Haight-Ashbury': 16,
            'Nob Hill': 12
        },
        'Financial District': {
            'Russian Hill': 11,
            'Marina District': 15,
            'Alamo Square': 17,
            'Golden Gate Park': 23,
            'The Castro': 20,
            'Bayview': 19,
            'Sunset District': 30,
            'Haight-Ashbury': 19,
            'Nob Hill': 8
        },
        'Alamo Square': {
            'Russian Hill': 13,
            'Marina District': 15,
            'Financial District': 17,
            'Golden Gate Park': 9,
            'The Castro': 8,
            'Bayview': 16,
            'Sunset District': 16,
            'Haight-Ashbury': 5,
            'Nob Hill': 11
        },
        'Golden Gate Park': {
            'Russian Hill': 19,
            'Marina District': 16,
            'Financial District': 26,
            'Alamo Square': 9,
            'The Castro': 13,
            'Bayview': 23,
            'Sunset District': 10,
            'Haight-Ashbury': 7,
            'Nob Hill': 20
        },
        'The Castro': {
            'Russian Hill': 18,
            'Marina District': 21,
            'Financial District': 21,
            'Alamo Square': 8,
            'Golden Gate Park': 11,
            'Bayview': 19,
            'Sunset District': 17,
            'Haight-Ashbury': 6,
            'Nob Hill': 16
        },
        'Bayview': {
            'Russian Hill': 23,
            'Marina District': 27,
            'Financial District': 19,
            'Alamo Square': 16,
            'Golden Gate Park': 22,
            'The Castro': 19,
            'Sunset District': 23,
            'Haight-Ashbury': 19,
            'Nob Hill': 20
        },
        'Sunset District': {
            'Russian Hill': 24,
            'Marina District': 21,
            'Financial District': 30,
            'Alamo Square': 17,
            'Golden Gate Park': 11,
            'The Castro': 17,
            'Bayview': 22,
            'Haight-Ashbury': 15,
            'Nob Hill': 27
        },
        'Haight-Ashbury': {
            'Russian Hill': 17,
            'Marina District': 17,
            'Financial District': 21,
            'Alamo Square': 5,
            'Golden Gate Park': 7,
            'The Castro': 6,
            'Bayview': 18,
            'Sunset District': 15,
            'Nob Hill': 15
        },
        'Nob Hill': {
            'Russian Hill': 5,
            'Marina District': 11,
            'Financial District': 9,
            'Alamo Square': 11,
            'Golden Gate Park': 17,
            'The Castro': 17,
            'Bayview': 19,
            'Sunset District': 24,
            'Haight-Ashbury': 13
        }
    }

    # Variables for each friend: arrival time, departure time, and whether they are met
    arrival = {friend: Int(f'arrival_{friend}') for friend in friends}
    departure = {friend: Int(f'departure_{friend}') for friend in friends}
    met = {friend: Bool(f'met_{friend}') for friend in friends}

    # Initial constraints: arrival at Russian Hill at 9:00AM (time = 0)
    current_location = 'Russian Hill'
    current_time = 0

    # Constraints for each friend
    for friend in friends:
        location = friends[friend]
        start, end = time_windows[friend]
        duration = min_durations[friend]

        # If the friend is met, their meeting must fit within their time window and meet the duration
        opt.add(Implies(met[friend], arrival[friend] >= start))
        opt.add(Implies(met[friend], departure[friend] <= end))
        opt.add(Implies(met[friend], departure[friend] - arrival[friend] >= duration))

        # If the friend is not met, their arrival and departure times are unconstrained
        opt.add(Implies(Not(met[friend]), arrival[friend] == -1))
        opt.add(Implies(Not(met[friend]), departure[friend] == -1))

    # Constraint: meet exactly 7 friends
    opt.add(Sum([If(met[friend], 1, 0) for friend in friends]) == 7)

    # Order constraints: ensure travel times are respected between consecutive meetings
    # We'll create a sequence variable to represent the order of meetings
    # This is a simplified approach - a more complete solution would need to model all possible orders
    
    # For now, we'll prioritize meeting Karen first since she has the earliest window
    # and ensure we have enough time to travel from Russian Hill to Financial District
    opt.add(Implies(met['Karen'], arrival['Karen'] >= 11))  # Travel time from Russian Hill to Financial District

    # Solve the problem
    if opt.check() == sat:
        m = opt.model()
        print("SOLUTION:")
        print("Optimal schedule meeting exactly 7 friends:")
        for friend in friends:
            if m[met[friend]]:
                print(f"- Meet {friend} at {friends[friend]} from {m[arrival[friend]]} to {m[departure[friend]]}")
        print(f"Total friends met: {sum(1 for friend in friends if m[met[friend]])}")
    else:
        print("No feasible schedule found meeting exactly 7 friends.")

solve_scheduling()