from z3 import *
import json

def main():
    # Convert time string to minutes since 9:00 AM
    def time_to_minutes(t):
        parts = t.split(':')
        hour = int(parts[0])
        minute = int(parts[1])
        return (hour - 9) * 60 + minute

    # Convert minutes back to time string
    def minutes_to_time(m):
        total_minutes = int(round(m))
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{9 + hours}:{minutes:02d}"

    # Define travel times dictionary
    travel_times = {
        ('Financial District', 'Golden Gate Park'): 23,
        ('Financial District', 'Chinatown'): 5,
        ('Financial District', 'Union Square'): 9,
        ('Financial District', 'Fisherman\'s Wharf'): 10,
        ('Financial District', 'Pacific Heights'): 13,
        ('Financial District', 'North Beach'): 7,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Golden Gate Park', 'Union Square'): 22,
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
        ('Golden Gate Park', 'Pacific Heights'): 16,
        ('Golden Gate Park', 'North Beach'): 24,
        ('Chinatown', 'Financial District'): 5,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'Fisherman\'s Wharf'): 8,
        ('Chinatown', 'Pacific Heights'): 10,
        ('Chinatown', 'North Beach'): 3,
        ('Union Square', 'Financial District'): 9,
        ('Union Square', 'Golden Gate Park'): 22,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Fisherman\'s Wharf'): 15,
        ('Union Square', 'Pacific Heights'): 15,
        ('Union Square', 'North Beach'): 10,
        ('Fisherman\'s Wharf', 'Financial District'): 11,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
        ('Fisherman\'s Wharf', 'Chinatown'): 12,
        ('Fisherman\'s Wharf', 'Union Square'): 13,
        ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
        ('Fisherman\'s Wharf', 'North Beach'): 6,
        ('Pacific Heights', 'Financial District'): 13,
        ('Pacific Heights', 'Golden Gate Park'): 15,
        ('Pacific Heights', 'Chinatown'): 11,
        ('Pacific Heights', 'Union Square'): 12,
        ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
        ('Pacific Heights', 'North Beach'): 9,
        ('North Beach', 'Financial District'): 8,
        ('North Beach', 'Golden Gate Park'): 22,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Union Square'): 7,
        ('North Beach', 'Fisherman\'s Wharf'): 5,
        ('North Beach', 'Pacific Heights'): 8
    }

    # Define friends data
    friends = [
        {'name': 'Stephanie', 'location': 'Golden Gate Park', 
         'available_start': time_to_minutes('11:00'), 'available_end': time_to_minutes('15:00'), 
         'min_duration': 105},
        {'name': 'Karen', 'location': 'Chinatown', 
         'available_start': time_to_minutes('13:45'), 'available_end': time_to_minutes('16:30'), 
         'min_duration': 15},
        {'name': 'Brian', 'location': 'Union Square', 
         'available_start': time_to_minutes('15:00'), 'available_end': time_to_minutes('17:15'), 
         'min_duration': 30},
        {'name': 'Rebecca', 'location': 'Fisherman\'s Wharf', 
         'available_start': time_to_minutes('8:00'), 'available_end': time_to_minutes('11:15'), 
         'min_duration': 30},
        {'name': 'Joseph', 'location': 'Pacific Heights', 
         'available_start': time_to_minutes('8:15'), 'available_end': time_to_minutes('9:30'), 
         'min_duration': 60},
        {'name': 'Steven', 'location': 'North Beach', 
         'available_start': time_to_minutes('14:30'), 'available_end': time_to_minutes('20:45'), 
         'min_duration': 120}
    ]

    # Initialize Z3 solver and optimization
    opt = Optimize()
    s = Solver()

    # Create variables for each friend
    meeting_vars = []
    for friend in friends:
        meet_var = Bool(f"meet_{friend['name']}")
        start_var = Int(f"start_{friend['name']}")
        end_var = Int(f"end_{friend['name']}")
        meeting_vars.append({
            'name': friend['name'],
            'location': friend['location'],
            'meet_var': meet_var,
            'start_var': start_var,
            'end_var': end_var,
            'min_duration': friend['min_duration'],
            'available_start': friend['available_start'],
            'available_end': friend['available_end']
        })

    # Dummy meeting at start
    dummy_location = 'Financial District'
    dummy_start = 0
    dummy_end = 0

    # Constraints for each meeting
    for m in meeting_vars:
        # If meeting occurs, constraints on time and duration
        opt.add(Implies(m['meet_var'], m['start_var'] >= m['available_start']))
        opt.add(Implies(m['meet_var'], m['end_var'] <= m['available_end']))
        opt.add(Implies(m['meet_var'], m['end_var'] == m['start_var'] + m['min_duration']))
        # Travel from Financial District to meeting location
        travel_time = travel_times[(dummy_location, m['location'])]
        opt.add(Implies(m['meet_var'], m['start_var'] >= dummy_start + travel_time))

    # Constraints between every pair of meetings
    for i in range(len(meeting_vars)):
        for j in range(i + 1, len(meeting_vars)):
            m1 = meeting_vars[i]
            m2 = meeting_vars[j]
            travel_time1 = travel_times[(m1['location'], m2['location'])]
            travel_time2 = travel_times[(m2['location'], m1['location'])]
            # If both meetings occur, they must not overlap and include travel
            opt.add(Implies(And(m1['meet_var'], m2['meet_var']),
                          Or(m2['start_var'] >= m1['end_var'] + travel_time1,
                             m1['start_var'] >= m2['end_var'] + travel_time2)))

    # Maximize the number of meetings
    meet_count = Sum([If(m['meet_var'], 1, 0) for m in meeting_vars])
    opt.maximize(meet_count)

    # Check for a solution
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        # Collect all scheduled meetings
        scheduled_meetings = []
        for m in meeting_vars:
            if model.eval(m['meet_var']):
                start_val = model.eval(m['start_var']).as_long()
                end_val = model.eval(m['end_var']).as_long()
                scheduled_meetings.append({
                    'name': m['name'],
                    'location': m['location'],
                    'start': start_val,
                    'end': end_val
                })
        # Sort meetings by start time
        scheduled_meetings.sort(key=lambda x: x['start'])
        # Convert to JSON output format
        for meeting in scheduled_meetings:
            itinerary.append({
                "action": "meet",
                "location": meeting['location'],
                "person": meeting['name'],
                "start_time": minutes_to_time(meeting['start']),
                "end_time": minutes_to_time(meeting['end'])
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()