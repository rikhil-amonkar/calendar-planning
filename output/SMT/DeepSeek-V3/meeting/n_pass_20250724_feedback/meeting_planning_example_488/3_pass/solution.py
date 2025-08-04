from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Define travel times (in minutes)
    travel_times = {
        ('Pacific Heights', 'Nob Hill'): 8,
        ('Pacific Heights', 'Russian Hill'): 7,
        ('Pacific Heights', 'The Castro'): 16,
        ('Pacific Heights', 'Sunset District'): 21,
        ('Pacific Heights', 'Haight-Ashbury'): 11,
        ('Nob Hill', 'Pacific Heights'): 8,
        ('Nob Hill', 'Russian Hill'): 5,
        ('Nob Hill', 'The Castro'): 17,
        ('Nob Hill', 'Sunset District'): 25,
        ('Nob Hill', 'Haight-Ashbury'): 13,
        ('Russian Hill', 'Pacific Heights'): 7,
        ('Russian Hill', 'Nob Hill'): 5,
        ('Russian Hill', 'The Castro'): 21,
        ('Russian Hill', 'Sunset District'): 23,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('The Castro', 'Pacific Heights'): 16,
        ('The Castro', 'Nob Hill'): 16,
        ('The Castro', 'Russian Hill'): 18,
        ('The Castro', 'Sunset District'): 17,
        ('The Castro', 'Haight-Ashbury'): 6,
        ('Sunset District', 'Pacific Heights'): 21,
        ('Sunset District', 'Nob Hill'): 27,
        ('Sunset District', 'Russian Hill'): 24,
        ('Sunset District', 'The Castro'): 17,
        ('Sunset District', 'Haight-Ashbury'): 15,
        ('Haight-Ashbury', 'Pacific Heights'): 12,
        ('Haight-Ashbury', 'Nob Hill'): 15,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Haight-Ashbury', 'The Castro'): 6,
        ('Haight-Ashbury', 'Sunset District'): 15
    }

    # Friends' availability and constraints
    friends = [
        {
            'name': 'Ronald',
            'location': 'Nob Hill',
            'available_start': 10 * 60,  # 10:00 AM in minutes
            'available_end': 17 * 60,    # 5:00 PM in minutes
            'min_duration': 105
        },
        {
            'name': 'Sarah',
            'location': 'Russian Hill',
            'available_start': 7 * 60 + 15,  # 7:15 AM in minutes
            'available_end': 9 * 60 + 30,     # 9:30 AM in minutes
            'min_duration': 45
        },
        {
            'name': 'Helen',
            'location': 'The Castro',
            'available_start': 13 * 60 + 30,  # 1:30 PM in minutes
            'available_end': 17 * 60,       # 5:00 PM in minutes
            'min_duration': 120
        },
        {
            'name': 'Joshua',
            'location': 'Sunset District',
            'available_start': 14 * 60 + 15,  # 2:15 PM in minutes
            'available_end': 19 * 60 + 30,    # 7:30 PM in minutes
            'min_duration': 90
        },
        {
            'name': 'Margaret',
            'location': 'Haight-Ashbury',
            'available_start': 10 * 60 + 15,  # 10:15 AM in minutes
            'available_end': 22 * 60,         # 10:00 PM in minutes
            'min_duration': 60
        }
    ]

    # Current location and time
    current_location = 'Pacific Heights'
    current_time = 9 * 60  # 9:00 AM in minutes

    # Variables for each meeting: start and end times
    meetings = {}
    for friend in friends:
        name = friend['name']
        meetings[name] = {
            'start': Int(f'start_{name}'),
            'end': Int(f'end_{name}'),
            'location': friend['location'],
            'min_duration': friend['min_duration'],
            'available_start': friend['available_start'],
            'available_end': friend['available_end']
        }

    # Constraints for each meeting
    for name, meeting in meetings.items():
        s.add(meeting['start'] >= meeting['available_start'])
        s.add(meeting['end'] <= meeting['available_end'])
        s.add(meeting['end'] == meeting['start'] + meeting['min_duration'])
        s.add(meeting['start'] >= 0)
        s.add(meeting['end'] >= 0)

    # Define order variables to determine the sequence of meetings
    order = {name: Int(f'order_{name}') for name in meetings}
    s.add(Distinct([order[name] for name in meetings]))
    for name in meetings:
        s.add(order[name] >= 0)
        s.add(order[name] < len(meetings))

    # Constraints to ensure travel times between consecutive meetings
    for name1 in meetings:
        for name2 in meetings:
            if name1 != name2:
                # If meeting1 is before meeting2 in the order
                s.add(Implies(order[name1] < order[name2],
                            meetings[name2]['start'] >= meetings[name1]['end'] + 
                            travel_times[(meetings[name1]['location'], meetings[name2]['location'])]))

    # Initial travel from Pacific Heights to the first meeting
    # Ensure that the first meeting starts after the initial travel time
    for name in meetings:
        s.add(Implies(order[name] == 0,
                     meetings[name]['start'] >= current_time + 
                     travel_times[(current_location, meetings[name]['location'])]))

    # Maximize the number of friends met (all friends have to be met)
    # Since all friends have to be met, we don't need to maximize, just satisfy constraints
    # But we can add a dummy objective to ensure the solver finds a solution
    s.minimize(0)

    # Check if all meetings can be scheduled
    if s.check() == sat:
        model = s.model()
        itinerary = []
        
        # Collect all meetings with their times and order
        scheduled_meetings = []
        for name in meetings:
            start = model[meetings[name]['start']].as_long()
            end = model[meetings[name]['end']].as_long()
            ord = model[order[name]].as_long()
            scheduled_meetings.append({
                'name': name,
                'start': start,
                'end': end,
                'order': ord
            })
        
        # Sort meetings by order
        scheduled_meetings.sort(key=lambda x: x['order'])
        
        # Convert to itinerary format
        for meeting in scheduled_meetings:
            start_hh = meeting['start'] // 60
            start_mm = meeting['start'] % 60
            end_hh = meeting['end'] // 60
            end_mm = meeting['end'] % 60
            itinerary.append({
                "action": "meet",
                "person": meeting['name'],
                "start_time": f"{start_hh:02d}:{start_mm:02d}",
                "end_time": f"{end_hh:02d}:{end_mm:02d}"
            })
        
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Run the solver and print the result
result = solve_scheduling()
print(json.dumps(result, indent=2))