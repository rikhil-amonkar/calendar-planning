from z3 import *

def solve_scheduling():
    # Initialize optimizer
    opt = Optimize()

    # Friends and their details
    friends = {
        'Mary': {
            'location': 'Pacific Heights',
            'available_start': 10 * 60,  # 10:00 AM in minutes
            'available_end': 19 * 60,    # 7:00 PM in minutes
            'min_duration': 45,
        },
        'Lisa': {
            'location': 'Mission District',
            'available_start': 20 * 60 + 30,  # 8:30 PM in minutes
            'available_end': 22 * 60,         # 10:00 PM in minutes
            'min_duration': 75,
        },
        'Betty': {
            'location': 'Haight-Ashbury',
            'available_start': 7 * 60 + 15,    # 7:15 AM in minutes
            'available_end': 17 * 60 + 15,     # 5:15 PM in minutes
            'min_duration': 90,
        },
        'Charles': {
            'location': 'Financial District',
            'available_start': 11 * 60 + 15,  # 11:15 AM in minutes
            'available_end': 15 * 60,         # 3:00 PM in minutes
            'min_duration': 120,
        }
    }

    # Travel times matrix (in minutes)
    travel_times = {
        ('Bayview', 'Pacific Heights'): 23,
        ('Bayview', 'Mission District'): 13,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'Financial District'): 19,
        ('Pacific Heights', 'Bayview'): 22,
        ('Pacific Heights', 'Mission District'): 15,
        ('Pacific Heights', 'Haight-Ashbury'): 11,
        ('Pacific Heights', 'Financial District'): 13,
        ('Mission District', 'Bayview'): 15,
        ('Mission District', 'Pacific Heights'): 16,
        ('Mission District', 'Haight-Ashbury'): 12,
        ('Mission District', 'Financial District'): 17,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Haight-Ashbury', 'Pacific Heights'): 12,
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Financial District'): 21,
        ('Financial District', 'Bayview'): 19,
        ('Financial District', 'Pacific Heights'): 13,
        ('Financial District', 'Mission District'): 17,
        ('Financial District', 'Haight-Ashbury'): 19,
    }

    # Variables for each friend's meeting start and end times, and whether they are scheduled
    meeting_vars = {}
    for name in friends:
        meeting_vars[name] = {
            'start': Int(f'start_{name}'),
            'end': Int(f'end_{name}'),
            'scheduled': Bool(f'scheduled_{name}')
        }

    # Current location starts at Bayview at 9:00 AM (540 minutes)
    current_time = 9 * 60  # 9:00 AM in minutes
    current_location = 'Bayview'

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        var = meeting_vars[name]
        opt.add(Implies(var['scheduled'], var['start'] >= friend['available_start']))
        opt.add(Implies(var['scheduled'], var['end'] <= friend['available_end']))
        opt.add(Implies(var['scheduled'], var['end'] == var['start'] + friend['min_duration']))
        opt.add(Implies(Not(var['scheduled']), var['start'] == -1))
        opt.add(Implies(Not(var['scheduled']), var['end'] == -1))

    # Ensure meetings do not overlap and travel times are respected
    scheduled_names = [name for name in friends]
    for i in range(len(scheduled_names)):
        for j in range(i + 1, len(scheduled_names)):
            name1 = scheduled_names[i]
            name2 = scheduled_names[j]
            loc1 = friends[name1]['location']
            loc2 = friends[name2]['location']
            travel_time = travel_times.get((loc1, loc2), 0)

            # Either meeting1 is before meeting2 with travel time, or vice versa
            opt.add(Implies(
                And(meeting_vars[name1]['scheduled'], meeting_vars[name2]['scheduled']),
                Or(
                    meeting_vars[name1]['end'] + travel_time <= meeting_vars[name2]['start'],
                    meeting_vars[name2]['end'] + travel_times.get((loc2, loc1), 0) <= meeting_vars[name1]['start']
                )
            ))

    # The first meeting must start after current_time + travel time from Bayview
    for name in friends:
        loc = friends[name]['location']
        travel_time = travel_times.get((current_location, loc), 0)
        opt.add(Implies(
            meeting_vars[name]['scheduled'],
            meeting_vars[name]['start'] >= current_time + travel_time
        ))

    # Maximize the number of scheduled meetings
    num_scheduled = Sum([If(meeting_vars[name]['scheduled'], 1, 0) for name in friends])
    opt.maximize(num_scheduled)

    # Check for a solution
    if opt.check() == sat:
        m = opt.model()
        scheduled_meetings = []
        for name in friends:
            if m.evaluate(meeting_vars[name]['scheduled']):
                start = m.evaluate(meeting_vars[name]['start']).as_long()
                end = m.evaluate(meeting_vars[name]['end']).as_long()
                scheduled_meetings.append({
                    'name': name,
                    'location': friends[name]['location'],
                    'start': start,
                    'end': end,
                    'duration': friends[name]['min_duration']
                })
        # Sort meetings by start time
        scheduled_meetings.sort(key=lambda x: x['start'])
        return scheduled_meetings
    else:
        return None

# Solve and print the schedule
schedule = solve_scheduling()
if schedule:
    print("SOLUTION:")
    print("Optimal Schedule:")
    for meeting in schedule:
        start_h = meeting['start'] // 60
        start_m = meeting['start'] % 60
        end_h = meeting['end'] // 60
        end_m = meeting['end'] % 60
        print(f"Meet {meeting['name']} at {meeting['location']} from {start_h:02d}:{start_m:02d} to {end_h:02d}:{end_m:02d}")
    print(f"Total friends met: {len(schedule)}")
else:
    print("No feasible schedule found.")