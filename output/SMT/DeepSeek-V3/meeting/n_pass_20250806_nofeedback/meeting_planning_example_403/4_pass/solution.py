from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Optimize()

    # Define variables for each meeting's start and end times (in minutes since 9:00 AM)
    andrew_start = Int('andrew_start')
    andrew_end = Int('andrew_end')
    sarah_start = Int('sarah_start')
    sarah_end = Int('sarah_end')
    nancy_start = Int('nancy_start')
    nancy_end = Int('nancy_end')
    rebecca_start = Int('rebecca_start')
    rebecca_end = Int('rebecca_end')
    robert_start = Int('robert_start')
    robert_end = Int('robert_end')

    # Convert friends' availability windows to minutes since 9:00 AM
    # Andrew: 11:45 AM (2h45m after 9:00 AM) to 2:30 PM (5h30m after)
    andrew_min_start = (11*60 + 45) - (9*60)  # 165 minutes
    andrew_max_end = (14*60 + 30) - (9*60)    # 330 minutes

    # Sarah: 4:15 PM (7h15m after 9:00 AM) to 6:45 PM (9h45m after)
    sarah_min_start = (16*60 + 15) - (9*60)   # 435 minutes
    sarah_max_end = (18*60 + 45) - (9*60)     # 585 minutes

    # Nancy: 5:30 PM (8h30m after 9:00 AM) to 7:15 PM (10h15m after)
    nancy_min_start = (17*60 + 30) - (9*60)   # 510 minutes
    nancy_max_end = (19*60 + 15) - (9*60)     # 615 minutes

    # Rebecca: 9:45 AM (45m after 9:00 AM) to 9:30 PM (12h30m after)
    rebecca_min_start = (9*60 + 45) - (9*60)  # 45 minutes
    rebecca_max_end = (21*60 + 30) - (9*60)   # 750 minutes

    # Robert: 8:30 AM (before 9:00 AM, but earliest possible is 9:00 AM) to 2:15 PM (5h15m after)
    robert_min_start = 0  # since 9:00 AM is the earliest possible start
    robert_max_end = (14*60 + 15) - (9*60)    # 315 minutes

    # Add constraints for each meeting's duration and availability window
    s.add(andrew_start >= andrew_min_start)
    s.add(andrew_end <= andrew_max_end)
    s.add(andrew_end - andrew_start >= 75)  # 75 minutes

    s.add(sarah_start >= sarah_min_start)
    s.add(sarah_end <= sarah_max_end)
    s.add(sarah_end - sarah_start >= 15)    # 15 minutes

    s.add(nancy_start >= nancy_min_start)
    s.add(nancy_end <= nancy_max_end)
    s.add(nancy_end - nancy_start >= 60)    # 60 minutes

    s.add(rebecca_start >= rebecca_min_start)
    s.add(rebecca_end <= rebecca_max_end)
    s.add(rebecca_end - rebecca_start >= 90) # 90 minutes

    s.add(robert_start >= robert_min_start)
    s.add(robert_end <= robert_max_end)
    s.add(robert_end - robert_start >= 30)   # 30 minutes

    # Define travel times between locations (in minutes)
    travel_times = {
        ('Union Square', 'Chinatown'): 7,
        ('Chinatown', 'The Castro'): 20,
        ('The Castro', 'Golden Gate Park'): 11,
        ('Golden Gate Park', 'Pacific Heights'): 16,
        ('Pacific Heights', 'Presidio'): 11,
        ('Chinatown', 'Union Square'): 7,
        ('The Castro', 'Union Square'): 19,
        ('Golden Gate Park', 'Union Square'): 22,
        ('Pacific Heights', 'Union Square'): 12,
        ('Presidio', 'Union Square'): 22
    }

    # Define meeting locations
    locations = {
        'Rebecca': 'Chinatown',
        'Robert': 'The Castro',
        'Andrew': 'Golden Gate Park',
        'Sarah': 'Pacific Heights',
        'Nancy': 'Presidio'
    }

    # Define the order of meetings
    # We'll try to meet Rebecca first, then Robert, then Andrew, then Sarah, then Nancy
    # This is a reasonable order based on availability windows and travel times

    # Start at Union Square at 9:00 AM (0 minutes)
    current_location = 'Union Square'
    current_time = 0

    # Meet Rebecca first (earliest available)
    s.add(rebecca_start >= current_time + travel_times[(current_location, locations['Rebecca'])])
    current_time = rebecca_end
    current_location = locations['Rebecca']

    # Then meet Robert
    s.add(robert_start >= current_time + travel_times[(current_location, locations['Robert'])])
    current_time = robert_end
    current_location = locations['Robert']

    # Then meet Andrew
    s.add(andrew_start >= current_time + travel_times[(current_location, locations['Andrew'])])
    current_time = andrew_end
    current_location = locations['Andrew']

    # Then meet Sarah
    s.add(sarah_start >= current_time + travel_times[(current_location, locations['Sarah'])])
    current_time = sarah_end
    current_location = locations['Sarah']

    # Finally meet Nancy
    s.add(nancy_start >= current_time + travel_times[(current_location, locations['Nancy'])])

    # To ensure we meet all friends, we'll maximize the number of meetings
    # (though in this case we're trying to meet all 5 friends)
    s.maximize(And(
        rebecca_end - rebecca_start >= 90,
        robert_end - robert_start >= 30,
        andrew_end - andrew_start >= 75,
        sarah_end - sarah_start >= 15,
        nancy_end - nancy_start >= 60
    ))

    # Check if the schedule is feasible
    if s.check() == sat:
        m = s.model()
        # Convert times back to HH:MM format
        def minutes_to_time(minutes):
            total_minutes = 9 * 60 + minutes
            h = total_minutes // 60
            m = total_minutes % 60
            return f"{h:02d}:{m:02d}"

        itinerary = [
            {"action": "meet", "person": "Rebecca", "start_time": minutes_to_time(m[rebecca_start].as_long()), "end_time": minutes_to_time(m[rebecca_end].as_long())},
            {"action": "meet", "person": "Robert", "start_time": minutes_to_time(m[robert_start].as_long()), "end_time": minutes_to_time(m[robert_end].as_long())},
            {"action": "meet", "person": "Andrew", "start_time": minutes_to_time(m[andrew_start].as_long()), "end_time": minutes_to_time(m[andrew_end].as_long())},
            {"action": "meet", "person": "Sarah", "start_time": minutes_to_time(m[sarah_start].as_long()), "end_time": minutes_to_time(m[sarah_end].as_long())},
            {"action": "meet", "person": "Nancy", "start_time": minutes_to_time(m[nancy_start].as_long()), "end_time": minutes_to_time(m[nancy_end].as_long())}
        ]
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

# Execute the solver and print the result
result = solve_scheduling()
print(json.dumps(result, indent=2))