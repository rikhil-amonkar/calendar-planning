from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Convert all times to minutes since 9:00 AM (0 minutes)
    # Friends' availability windows in minutes since 9:00 AM
    andrew_start = 165  # 11:45AM
    andrew_end = 330    # 2:30PM
    sarah_start = 435   # 4:15PM
    sarah_end = 525     # 6:45PM
    nancy_start = 510   # 5:30PM
    nancy_end = 555     # 7:15PM
    rebecca_start = 45  # 9:45AM
    rebecca_end = 750   # 9:30PM
    robert_start = 0    # 9:00AM (adjusted from 8:30AM)
    robert_end = 315    # 2:15PM

    # Meeting durations in minutes
    andrew_min_duration = 75
    sarah_min_duration = 15
    nancy_min_duration = 60
    rebecca_min_duration = 90
    robert_min_duration = 30

    # Variables for start and end times of each meeting
    andrew_start_var = Real('andrew_start')
    andrew_end_var = Real('andrew_end')
    sarah_start_var = Real('sarah_start')
    sarah_end_var = Real('sarah_end')
    nancy_start_var = Real('nancy_start')
    nancy_end_var = Real('nancy_end')
    rebecca_start_var = Real('rebecca_start')
    rebecca_end_var = Real('rebecca_end')
    robert_start_var = Real('robert_start')
    robert_end_var = Real('robert_end')

    # Constraints for each meeting
    # Andrew
    s.add(andrew_start_var >= andrew_start)
    s.add(andrew_end_var <= andrew_end)
    s.add(andrew_end_var - andrew_start_var >= andrew_min_duration)
    # Sarah
    s.add(sarah_start_var >= sarah_start)
    s.add(sarah_end_var <= sarah_end)
    s.add(sarah_end_var - sarah_start_var >= sarah_min_duration)
    # Nancy
    s.add(nancy_start_var >= nancy_start)
    s.add(nancy_end_var <= nancy_end)
    s.add(nancy_end_var - nancy_start_var >= nancy_min_duration)
    # Rebecca
    s.add(rebecca_start_var >= rebecca_start)
    s.add(rebecca_end_var <= rebecca_end)
    s.add(rebecca_end_var - rebecca_start_var >= rebecca_min_duration)
    # Robert
    s.add(robert_start_var >= robert_start)
    s.add(robert_end_var <= robert_end)
    s.add(robert_end_var - robert_start_var >= robert_min_duration)

    # Travel times dictionary
    travel_times = {
        'Union Square': {'Golden Gate Park': 22, 'Pacific Heights': 15, 'Presidio': 24, 'Chinatown': 7, 'The Castro': 19},
        'Golden Gate Park': {'Union Square': 22, 'Pacific Heights': 16, 'Presidio': 11, 'Chinatown': 23, 'The Castro': 13},
        'Pacific Heights': {'Union Square': 12, 'Golden Gate Park': 15, 'Presidio': 11, 'Chinatown': 11, 'The Castro': 16},
        'Presidio': {'Union Square': 22, 'Golden Gate Park': 12, 'Pacific Heights': 11, 'Chinatown': 21, 'The Castro': 21},
        'Chinatown': {'Union Square': 7, 'Golden Gate Park': 23, 'Pacific Heights': 10, 'Presidio': 19, 'The Castro': 22},
        'The Castro': {'Union Square': 19, 'Golden Gate Park': 11, 'Pacific Heights': 16, 'Presidio': 20, 'Chinatown': 20}
    }

    # Assume visiting order: Robert -> Rebecca -> Andrew -> Sarah -> Nancy
    # Start at Union Square at time 0
    s.add(robert_start_var >= travel_times['Union Square']['The Castro'])
    s.add(rebecca_start_var >= robert_end_var + travel_times['The Castro']['Chinatown'])
    s.add(andrew_start_var >= rebecca_end_var + travel_times['Chinatown']['Golden Gate Park'])
    s.add(sarah_start_var >= andrew_end_var + travel_times['Golden Gate Park']['Pacific Heights'])
    s.add(nancy_start_var >= sarah_end_var + travel_times['Pacific Heights']['Presidio'])

    # Check feasibility
    if s.check() == sat:
        m = s.model()
        print("Feasible schedule found:")
        
        def format_time(minutes):
            total_minutes = int(m[minutes].as_long())
            hours = total_minutes // 60
            mins = total_minutes % 60
            ampm = "AM" if hours < 12 else "PM"
            if hours > 12:
                hours -= 12
            return f"{hours}:{mins:02d} {ampm}"
        
        print(f"Meet Robert at The Castro: {format_time(robert_start_var)} to {format_time(robert_end_var)}")
        print(f"Meet Rebecca at Chinatown: {format_time(rebecca_start_var)} to {format_time(rebecca_end_var)}")
        print(f"Meet Andrew at Golden Gate Park: {format_time(andrew_start_var)} to {format_time(andrew_end_var)}")
        print(f"Meet Sarah at Pacific Heights: {format_time(sarah_start_var)} to {format_time(sarah_end_var)}")
        print(f"Meet Nancy at Presidio: {format_time(nancy_start_var)} to {format_time(nancy_end_var)}")
    else:
        print("No feasible schedule found with the assumed order.")

solve_scheduling()