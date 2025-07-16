from z3 import *

def solve_scheduling():
    s = Solver()

    # Define friends and their details
    friends = {
        'Betty': {
            'location': 'Russian Hill',
            'available_start': 7 * 60,
            'available_end': 16 * 60 + 45,
            'min_duration': 105,
        },
        'Melissa': {
            'location': 'Alamo Square',
            'available_start': 9 * 60 + 30,
            'available_end': 17 * 60 + 15,
            'min_duration': 105,
        },
        'Joshua': {
            'location': 'Haight-Ashbury',
            'available_start': 12 * 60 + 15,
            'available_end': 19 * 60,
            'min_duration': 90,
        },
        'Jeffrey': {
            'location': 'Marina District',
            'available_start': 12 * 60 + 15,
            'available_end': 18 * 60,
            'min_duration': 45,
        },
        'James': {
            'location': 'Bayview',
            'available_start': 7 * 60 + 30,
            'available_end': 20 * 60,
            'min_duration': 90,
        },
        'Anthony': {
            'location': 'Chinatown',
            'available_start': 11 * 60 + 45,
            'available_end': 13 * 60 + 30,
            'min_duration': 75,
        },
        'Timothy': {
            'location': 'Presidio',
            'available_start': 12 * 60 + 30,
            'available_end': 14 * 60 + 45,
            'min_duration': 90,
        },
        'Emily': {
            'location': 'Sunset District',
            'available_start': 19 * 60 + 30,
            'available_end': 21 * 60 + 30,
            'min_duration': 120,
        }
    }

    # Complete travel times matrix
    travel_times = {
        ('Union Square', 'Russian Hill'): 13,
        ('Union Square', 'Alamo Square'): 15,
        ('Union Square', 'Haight-Ashbury'): 18,
        ('Union Square', 'Marina District'): 18,
        ('Union Square', 'Bayview'): 15,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Presidio'): 24,
        ('Union Square', 'Sunset District'): 27,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'Marina District'): 7,
        ('Russian Hill', 'Bayview'): 23,
        ('Russian Hill', 'Chinatown'): 9,
        ('Russian Hill', 'Presidio'): 14,
        ('Russian Hill', 'Sunset District'): 23,
        ('Alamo Square', 'Haight-Ashbury'): 5,
        ('Alamo Square', 'Marina District'): 15,
        ('Alamo Square', 'Bayview'): 16,
        ('Alamo Square', 'Chinatown'): 15,
        ('Alamo Square', 'Presidio'): 17,
        ('Alamo Square', 'Sunset District'): 16,
        ('Haight-Ashbury', 'Marina District'): 17,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Haight-Ashbury', 'Chinatown'): 19,
        ('Haight-Ashbury', 'Presidio'): 15,
        ('Haight-Ashbury', 'Sunset District'): 15,
        ('Marina District', 'Bayview'): 27,
        ('Marina District', 'Chinatown'): 15,
        ('Marina District', 'Presidio'): 10,
        ('Marina District', 'Sunset District'): 19,
        ('Bayview', 'Chinatown'): 19,
        ('Bayview', 'Presidio'): 32,
        ('Bayview', 'Sunset District'): 23,
        ('Chinatown', 'Presidio'): 19,
        ('Chinatown', 'Sunset District'): 29,
        ('Presidio', 'Sunset District'): 16,
    }

    # Create meeting variables
    meeting_vars = {}
    for name in friends:
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        meeting_vars[name] = {'start': start, 'end': end}

    # Current location and time
    current_location = 'Union Square'
    current_time = 9 * 60  # 9:00 AM

    # Basic constraints for each meeting
    for name, details in friends.items():
        s.add(meeting_vars[name]['start'] >= details['available_start'])
        s.add(meeting_vars[name]['end'] <= details['available_end'])
        s.add(meeting_vars[name]['end'] - meeting_vars[name]['start'] >= details['min_duration'])

    # Generate all possible meeting orders
    friend_names = list(friends.keys())
    for i in range(len(friend_names)):
        for j in range(i+1, len(friend_names)):
            name1 = friend_names[i]
            name2 = friend_names[j]
            loc1 = friends[name1]['location']
            loc2 = friends[name2]['location']
            
            travel_time = travel_times.get((loc1, loc2), 0)
            
            # Either meeting1 is before meeting2 with travel time
            option1 = And(
                meeting_vars[name1]['end'] + travel_time <= meeting_vars[name2]['start']
            )
            
            # Or meeting2 is before meeting1 with travel time
            option2 = And(
                meeting_vars[name2]['end'] + travel_times.get((loc2, loc1), 0) <= meeting_vars[name1]['start']
            )
            
            s.add(Or(option1, option2))

    # Ensure first meeting starts after arrival
    for name in friends:
        loc = friends[name]['location']
        travel_time = travel_times.get((current_location, loc), 0)
        s.add(meeting_vars[name]['start'] >= current_time + travel_time)

    # Try to solve
    if s.check() == sat:
        m = s.model()
        schedule = []
        for name in friends:
            start_val = m[meeting_vars[name]['start']]
            end_val = m[meeting_vars[name]['end']]
            
            if start_val is None or end_val is None:
                continue
                
            start = start_val.as_long()
            end = end_val.as_long()
            
            schedule.append({
                'name': name,
                'location': friends[name]['location'],
                'start': f"{start//60}:{start%60:02d}",
                'end': f"{end//60}:{end%60:02d}",
                'duration': end - start
            })
        
        # Sort schedule by start time
        schedule.sort(key=lambda x: int(x['start'].split(':')[0])*60 + int(x['start'].split(':')[1]))
        
        # Verify all meetings are included
        if len(schedule) == len(friends):
            return schedule
    return None

schedule = solve_scheduling()
if schedule:
    print("SOLUTION:")
    for meeting in schedule:
        print(f"Meet {meeting['name']} at {meeting['location']} from {meeting['start']} to {meeting['end']} (duration: {meeting['duration']} minutes)")
else:
    print("No valid schedule found that meets all constraints.")