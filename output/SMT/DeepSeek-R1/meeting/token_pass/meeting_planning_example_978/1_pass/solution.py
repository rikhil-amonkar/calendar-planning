from z3 import *
import json

def main():
    # Convert time string to minutes since midnight
    def time_to_minutes(t_str):
        time, period = t_str[:-2], t_str[-2:]
        hours, minutes = time.split(':')
        h = int(hours)
        m = int(minutes)
        if period == 'PM' and h != 12:
            h += 12
        if period == 'AM' and h == 12:
            h = 0
        return h * 60 + m

    # Travel times dictionary
    travel_time = {
        'Embarcadero': {
            'Embarcadero': 0,
            'Fisherman\'s Wharf': 6,
            'Financial District': 5,
            'Russian Hill': 8,
            'Marina District': 12,
            'Richmond District': 21,
            'Pacific Heights': 11,
            'Haight-Ashbury': 21,
            'Presidio': 20,
            'Nob Hill': 10,
            'The Castro': 25
        },
        'Fisherman\'s Wharf': {
            'Embarcadero': 8,
            'Fisherman\'s Wharf': 0,
            'Financial District': 11,
            'Russian Hill': 7,
            'Marina District': 9,
            'Richmond District': 18,
            'Pacific Heights': 12,
            'Haight-Ashbury': 22,
            'Presidio': 17,
            'Nob Hill': 11,
            'The Castro': 27
        },
        'Financial District': {
            'Embarcadero': 4,
            'Fisherman\'s Wharf': 10,
            'Financial District': 0,
            'Russian Hill': 11,
            'Marina District': 15,
            'Richmond District': 21,
            'Pacific Heights': 13,
            'Haight-Ashbury': 19,
            'Presidio': 22,
            'Nob Hill': 8,
            'The Castro': 20
        },
        'Russian Hill': {
            'Embarcadero': 8,
            'Fisherman\'s Wharf': 7,
            'Financial District': 11,
            'Russian Hill': 0,
            'Marina District': 7,
            'Richmond District': 14,
            'Pacific Heights': 7,
            'Haight-Ashbury': 17,
            'Presidio': 14,
            'Nob Hill': 5,
            'The Castro': 21
        },
        'Marina District': {
            'Embarcadero': 14,
            'Fisherman\'s Wharf': 10,
            'Financial District': 17,
            'Russian Hill': 8,
            'Marina District': 0,
            'Richmond District': 11,
            'Pacific Heights': 7,
            'Haight-Ashbury': 16,
            'Presidio': 10,
            'Nob Hill': 12,
            'The Castro': 22
        },
        'Richmond District': {
            'Embarcadero': 19,
            'Fisherman\'s Wharf': 18,
            'Financial District': 22,
            'Russian Hill': 13,
            'Marina District': 9,
            'Richmond District': 0,
            'Pacific Heights': 10,
            'Haight-Ashbury': 10,
            'Presidio': 7,
            'Nob Hill': 17,
            'The Castro': 16
        },
        'Pacific Heights': {
            'Embarcadero': 10,
            'Fisherman\'s Wharf': 13,
            'Financial District': 13,
            'Russian Hill': 7,
            'Marina District': 6,
            'Richmond District': 12,
            'Pacific Heights': 0,
            'Haight-Ashbury': 11,
            'Presidio': 11,
            'Nob Hill': 8,
            'The Castro': 16
        },
        'Haight-Ashbury': {
            'Embarcadero': 20,
            'Fisherman\'s Wharf': 23,
            'Financial District': 21,
            'Russian Hill': 17,
            'Marina District': 17,
            'Richmond District': 10,
            'Pacific Heights': 12,
            'Haight-Ashbury': 0,
            'Presidio': 15,
            'Nob Hill': 15,
            'The Castro': 6
        },
        'Presidio': {
            'Embarcadero': 20,
            'Fisherman\'s Wharf': 19,
            'Financial District': 23,
            'Russian Hill': 14,
            'Marina District': 11,
            'Richmond District': 7,
            'Pacific Heights': 11,
            'Haight-Ashbury': 15,
            'Presidio': 0,
            'Nob Hill': 18,
            'The Castro': 21
        },
        'Nob Hill': {
            'Embarcadero': 9,
            'Fisherman\'s Wharf': 10,
            'Financial District': 9,
            'Russian Hill': 5,
            'Marina District': 11,
            'Richmond District': 14,
            'Pacific Heights': 8,
            'Haight-Ashbury': 13,
            'Presidio': 17,
            'Nob Hill': 0,
            'The Castro': 17
        },
        'The Castro': {
            'Embarcadero': 22,
            'Fisherman\'s Wharf': 24,
            'Financial District': 21,
            'Russian Hill': 18,
            'Marina District': 21,
            'Richmond District': 16,
            'Pacific Heights': 16,
            'Haight-Ashbury': 6,
            'Presidio': 20,
            'Nob Hill': 16,
            'The Castro': 0
        }
    }

    # Friends data: name, location, available start, available end, min duration
    friends = [
        {'name': 'Stephanie', 'location': 'Fisherman\'s Wharf', 'start_avail': time_to_minutes('3:30PM'), 'end_avail': time_to_minutes('10:00PM'), 'min_dur': 30},
        {'name': 'Lisa', 'location': 'Financial District', 'start_avail': time_to_minutes('10:45AM'), 'end_avail': time_to_minutes('5:15PM'), 'min_dur': 15},
        {'name': 'Melissa', 'location': 'Russian Hill', 'start_avail': time_to_minutes('5:00PM'), 'end_avail': time_to_minutes('9:45PM'), 'min_dur': 120},
        {'name': 'Betty', 'location': 'Marina District', 'start_avail': time_to_minutes('10:45AM'), 'end_avail': time_to_minutes('2:15PM'), 'min_dur': 60},
        {'name': 'Sarah', 'location': 'Richmond District', 'start_avail': time_to_minutes('4:15PM'), 'end_avail': time_to_minutes('7:30PM'), 'min_dur': 105},
        {'name': 'Daniel', 'location': 'Pacific Heights', 'start_avail': time_to_minutes('6:30PM'), 'end_avail': time_to_minutes('9:45PM'), 'min_dur': 60},
        {'name': 'Joshua', 'location': 'Haight-Ashbury', 'start_avail': time_to_minutes('9:00AM'), 'end_avail': time_to_minutes('3:30PM'), 'min_dur': 15},
        {'name': 'Joseph', 'location': 'Presidio', 'start_avail': time_to_minutes('7:00AM'), 'end_avail': time_to_minutes('1:00PM'), 'min_dur': 45},
        {'name': 'Andrew', 'location': 'Nob Hill', 'start_avail': time_to_minutes('7:45PM'), 'end_avail': time_to_minutes('10:00PM'), 'min_dur': 105},
        {'name': 'John', 'location': 'The Castro', 'start_avail': time_to_minutes('1:15PM'), 'end_avail': time_to_minutes('7:45PM'), 'min_dur': 45}
    ]
    
    # Virtual start meeting at Embarcadero at 9:00AM
    virtual_meeting = {'name': 'Start', 'location': 'Embarcadero', 'start_avail': 540, 'end_avail': 540, 'min_dur': 0}
    meetings = [virtual_meeting] + friends
    n = len(meetings)
    
    # Z3 variables
    meet_vars = [Bool(f"meet_{i}") for i in range(n)]
    start_vars = [Real(f"start_{i}") for i in range(n)]
    end_vars = [Real(f"end_{i}") for i in range(n)]
    
    # Fixed virtual meeting
    constraints = [start_vars[0] == 540, end_vars[0] == 540, meet_vars[0] == True]
    
    # Constraints for each meeting
    for i in range(1, n):
        m = meetings[i]
        constraints.append(Implies(meet_vars[i], start_vars[i] >= m['start_avail']))
        constraints.append(Implies(meet_vars[i], end_vars[i] <= m['end_avail']))
        constraints.append(Implies(meet_vars[i], end_vars[i] - start_vars[i] >= m['min_dur']))
    
    # Travel constraints between all pairs of meetings
    for i in range(n):
        for j in range(i+1, n):
            loc_i = meetings[i]['location']
            loc_j = meetings[j]['location']
            travel_ij = travel_time[loc_i][loc_j]
            travel_ji = travel_time[loc_j][loc_i]
            constraints.append(Implies(And(meet_vars[i], meet_vars[j]),
                Or(end_vars[i] + travel_ij <= start_vars[j], end_vars[j] + travel_ji <= start_vars[i])))
    
    # Maximize the number of meetings
    opt = Optimize()
    opt.add(constraints)
    opt.maximize(Sum([If(meet_vars[i], 1, 0) for i in range(1, n)]))
    
    # Solve
    if opt.check() == sat:
        model = opt.model()
        held_meetings = []
        for i in range(1, n):
            if is_true(model.eval(meet_vars[i])):
                start_val = model.eval(start_vars[i])
                end_val = model.eval(end_vars[i])
                # Convert to integers
                start_minutes = int(str(start_val).split('/')[0]) if '/' in str(start_val) else int(float(str(start_val)))
                end_minutes = int(str(end_val).split('/')[0]) if '/' in str(end_val) else int(float(str(end_val)))
                held_meetings.append({
                    'name': meetings[i]['name'],
                    'location': meetings[i]['location'],
                    'start': start_minutes,
                    'end': end_minutes
                })
        
        # Sort by start time
        held_meetings.sort(key=lambda x: x['start'])
        
        # Convert minutes to time string
        def minutes_to_time(m):
            hours = m // 60
            minutes = m % 60
            period = 'AM' if hours < 12 else 'PM'
            if hours > 12:
                hours -= 12
            if hours == 0:
                hours = 12
            return f"{hours}:{minutes:02d}{period}"
        
        itinerary = []
        for m in held_meetings:
            itinerary.append({
                'action': 'meet',
                'location': m['location'],
                'person': m['name'],
                'start_time': minutes_to_time(m['start']),
                'end_time': minutes_to_time(m['end'])
            })
        
        result = {'itinerary': itinerary}
        print(json.dumps(result, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()