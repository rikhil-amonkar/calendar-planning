from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

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

    # Order constraints: meetings must be scheduled in some order with travel time
    # We need to model the sequence of meetings. This is complex, so we'll assume a fixed order for simplicity.
    # Alternatively, we can use a more sophisticated approach with Z3's sequencing constraints.
    # For this example, we'll try a specific order that might work.

    # Try meeting Sarah first (she's available earliest)
    sarah_meeting = meetings['Sarah']
    s.add(sarah_meeting['start'] >= current_time + travel_times[(current_location, sarah_meeting['location'])])

    # After Sarah, the next location is Russian Hill
    next_location = sarah_meeting['location']
    next_time = sarah_meeting['end']

    # Next, meet Margaret (she's available all day)
    margaret_meeting = meetings['Margaret']
    s.add(margaret_meeting['start'] >= next_time + travel_times[(next_location, margaret_meeting['location'])])

    # After Margaret, the next location is Haight-Ashbury
    next_location = margaret_meeting['location']
    next_time = margaret_meeting['end']

    # Next, meet Ronald
    ronald_meeting = meetings['Ronald']
    s.add(ronald_meeting['start'] >= next_time + travel_times[(next_location, ronald_meeting['location'])])

    # After Ronald, the next location is Nob Hill
    next_location = ronald_meeting['location']
    next_time = ronald_meeting['end']

    # Next, meet Helen
    helen_meeting = meetings['Helen']
    s.add(helen_meeting['start'] >= next_time + travel_times[(next_location, helen_meeting['location'])])

    # After Helen, the next location is The Castro
    next_location = helen_meeting['location']
    next_time = helen_meeting['end']

    # Finally, meet Joshua
    joshua_meeting = meetings['Joshua']
    s.add(joshua_meeting['start'] >= next_time + travel_times[(next_location, joshua_meeting['location'])])

    # Check if all meetings can be scheduled
    if s.check() == sat:
        model = s.model()
        itinerary = []
        
        # Collect all meetings with their times
        scheduled_meetings = []
        for name in meetings:
            start = model[meetings[name]['start']].as_long()
            end = model[meetings[name]['end']].as_long()
            scheduled_meetings.append({
                'name': name,
                'start': start,
                'end': end,
                'location': meetings[name]['location']
            })
        
        # Sort meetings by start time
        scheduled_meetings.sort(key=lambda x: x['start'])
        
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