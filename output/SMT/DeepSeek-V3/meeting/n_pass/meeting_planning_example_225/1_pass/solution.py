from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Locations
    locations = ['Sunset', 'NorthBeach', 'UnionSquare', 'AlamoSquare']
    
    # Travel times (in minutes) as a dictionary of dictionaries
    travel_times = {
        'Sunset': {'NorthBeach': 29, 'UnionSquare': 30, 'AlamoSquare': 17},
        'NorthBeach': {'Sunset': 27, 'UnionSquare': 7, 'AlamoSquare': 16},
        'UnionSquare': {'Sunset': 26, 'NorthBeach': 10, 'AlamoSquare': 15},
        'AlamoSquare': {'Sunset': 16, 'NorthBeach': 15, 'UnionSquare': 14}
    }

    # Convert all times to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(h, m):
        return h * 60 + m - 540  # 9:00 AM is 540 minutes since midnight

    # Friend constraints
    friends = {
        'Sarah': {
            'location': 'NorthBeach',
            'start': time_to_minutes(16, 0),  # 4:00 PM
            'end': time_to_minutes(18, 15),    # 6:15 PM
            'duration': 60                     # 60 minutes
        },
        'Jeffrey': {
            'location': 'UnionSquare',
            'start': time_to_minutes(15, 0),  # 3:00 PM
            'end': time_to_minutes(22, 0),    # 10:00 PM
            'duration': 75                     # 75 minutes
        },
        'Brian': {
            'location': 'AlamoSquare',
            'start': time_to_minutes(16, 0),   # 4:00 PM
            'end': time_to_minutes(17, 30),   # 5:30 PM
            'duration': 75                     # 75 minutes
        }
    }

    # Variables for each friend's meeting start and end times
    meeting_start = {name: Int(f'start_{name}') for name in friends}
    meeting_end = {name: Int(f'end_{name}') for name in friends}

    # Current location starts at Sunset District at time 0 (9:00 AM)
    current_location = 'Sunset'
    current_time = 0

    # Constraints for each friend's meeting
    for name in friends:
        friend = friends[name]
        s.add(meeting_start[name] >= friend['start'])
        s.add(meeting_end[name] <= friend['end'])
        s.add(meeting_end[name] == meeting_start[name] + friend['duration'])
        # Ensure meeting is within friend's availability
        s.add(meeting_start[name] >= friend['start'])
        s.add(meeting_end[name] <= friend['end'])

    # Constraints to ensure no overlapping meetings and travel times are accounted for
    # We'll prioritize meeting as many friends as possible, so we'll allow the solver to choose which meetings to attend
    # Here, we'll try to meet all three friends if possible

    # Order of meetings: since Brian and Sarah are at the same time, we need to choose between them
    # Let's try to meet Jeffrey first, then choose between Sarah and Brian

    # Option 1: Meet Jeffrey and Sarah
    s.push()
    s.add(meeting_start['Jeffrey'] + friends['Jeffrey']['duration'] + travel_times['UnionSquare']['NorthBeach'] <= meeting_start['Sarah'])
    s.add(meeting_start['Jeffrey'] >= travel_times['Sunset']['UnionSquare'])  # Travel from Sunset to UnionSquare

    # Option 2: Meet Jeffrey and Brian
    s.push()
    s.add(meeting_start['Jeffrey'] + friends['Jeffrey']['duration'] + travel_times['UnionSquare']['AlamoSquare'] <= meeting_start['Brian'])
    s.add(meeting_start['Jeffrey'] >= travel_times['Sunset']['UnionSquare'])  # Travel from Sunset to UnionSquare

    # Check which option is feasible
    if s.check() == sat:
        model = s.model()
        print("Feasible schedule found:")
        for name in friends:
            start = model[meeting_start[name]].as_long()
            end = model[meeting_end[name]].as_long()
            print(f"Meet {name} from {start + 540} minutes ({(start + 540) // 60}:{(start + 540) % 60}) to {end + 540} minutes ({(end + 540) // 60}:{(end + 540) % 60})")
    else:
        print("No feasible schedule found to meet all friends.")

    # Reset solver to try other options
    s.pop()

    # Try to meet only two friends if meeting all three is not possible
    # Option 1: Meet Jeffrey and Sarah
    s.push()
    s.add(meeting_start['Jeffrey'] + friends['Jeffrey']['duration'] + travel_times['UnionSquare']['NorthBeach'] <= meeting_start['Sarah'])
    s.add(meeting_start['Jeffrey'] >= travel_times['Sunset']['UnionSquare'])
    s.add(Or(meeting_start['Brian'] == -1, meeting_end['Brian'] == -1))  # Skip Brian

    if s.check() == sat:
        model = s.model()
        print("Feasible schedule (Jeffrey and Sarah):")
        for name in ['Jeffrey', 'Sarah']:
            start = model[meeting_start[name]].as_long()
            end = model[meeting_end[name]].as_long()
            print(f"Meet {name} from {start + 540} minutes ({(start + 540) // 60}:{(start + 540) % 60}) to {end + 540} minutes ({(end + 540) // 60}:{(end + 540) % 60})")
    else:
        print("No feasible schedule for Jeffrey and Sarah.")

    s.pop()

    # Option 2: Meet Jeffrey and Brian
    s.push()
    s.add(meeting_start['Jeffrey'] + friends['Jeffrey']['duration'] + travel_times['UnionSquare']['AlamoSquare'] <= meeting_start['Brian'])
    s.add(meeting_start['Jeffrey'] >= travel_times['Sunset']['UnionSquare'])
    s.add(Or(meeting_start['Sarah'] == -1, meeting_end['Sarah'] == -1))  # Skip Sarah

    if s.check() == sat:
        model = s.model()
        print("Feasible schedule (Jeffrey and Brian):")
        for name in ['Jeffrey', 'Brian']:
            start = model[meeting_start[name]].as_long()
            end = model[meeting_end[name]].as_long()
            print(f"Meet {name} from {start + 540} minutes ({(start + 540) // 60}:{(start + 540) % 60}) to {end + 540} minutes ({(end + 540) // 60}:{(end + 540) % 60})")
    else:
        print("No feasible schedule for Jeffrey and Brian.")

    s.pop()

    # Option 3: Meet Sarah and Brian (not possible due to overlapping times)
    s.push()
    s.add(Or(meeting_start['Jeffrey'] == -1, meeting_end['Jeffrey'] == -1))  # Skip Jeffrey
    s.add(meeting_start['Sarah'] + friends['Sarah']['duration'] + travel_times['NorthBeach']['AlamoSquare'] <= meeting_start['Brian'])
    s.add(meeting_start['Sarah'] >= travel_times['Sunset']['NorthBeach'])

    if s.check() == sat:
        model = s.model()
        print("Feasible schedule (Sarah and Brian):")
        for name in ['Sarah', 'Brian']:
            start = model[meeting_start[name]].as_long()
            end = model[meeting_end[name]].as_long()
            print(f"Meet {name} from {start + 540} minutes ({(start + 540) // 60}:{(start + 540) % 60}) to {end + 540} minutes ({(end + 540) // 60}:{(end + 540) % 60})")
    else:
        print("No feasible schedule for Sarah and Brian.")

    s.pop()

    # Finally, try to meet only one friend
    for name in friends:
        s.push()
        s.add(meeting_start[name] >= travel_times['Sunset'][friends[name]['location']])
        s.add(Or([meeting_start[n] == -1 for n in friends if n != name]))
        s.add(Or([meeting_end[n] == -1 for n in friends if n != name]))

        if s.check() == sat:
            model = s.model()
            print(f"Feasible schedule (only {name}):")
            start = model[meeting_start[name]].as_long()
            end = model[meeting_end[name]].as_long()
            print(f"Meet {name} from {start + 540} minutes ({(start + 540) // 60}:{(start + 540) % 60}) to {end + 540} minutes ({(end + 540) // 60}:{(end + 540) % 60})")
        else:
            print(f"No feasible schedule for {name}.")

        s.pop()

solve_scheduling()