from z3 import *
import json

def main():
    # Define the list of locations in order
    locations = [
        'Pacific Heights',
        'Golden Gate Park',
        'The Castro',
        'Bayview',
        'Marina District',
        'Union Square',
        'Sunset District',
        'Alamo Square',
        'Financial District',
        'Mission District'
    ]
    
    # Travel time matrix (10x10) in minutes between locations (indexed as above)
    travel_matrix = [
        [0, 15, 16, 22, 6, 12, 21, 10, 13, 15],
        [16, 0, 13, 23, 16, 22, 10, 9, 26, 17],
        [16, 11, 0, 19, 21, 19, 17, 8, 21, 7],
        [23, 22, 19, 0, 27, 18, 23, 16, 19, 13],
        [7, 18, 22, 27, 0, 16, 19, 15, 17, 20],
        [15, 22, 17, 15, 18, 0, 27, 15, 9, 14],
        [21, 11, 17, 22, 21, 30, 0, 17, 30, 25],
        [10, 9, 8, 16, 15, 14, 16, 0, 17, 10],
        [13, 23, 20, 19, 15, 9, 30, 17, 0, 17],
        [16, 17, 7, 14, 19, 15, 24, 11, 15, 0]
    ]
    
    # Friends data: name, location, start_avail (min from 9:00), end_avail (min from 9:00), min_dur
    friends = [
        {'name': 'Helen', 'location': 'Golden Gate Park', 'start_avail': 30, 'end_avail': 195, 'min_dur': 45},
        {'name': 'Steven', 'location': 'The Castro', 'start_avail': 675, 'end_avail': 780, 'min_dur': 105},
        {'name': 'Deborah', 'location': 'Bayview', 'start_avail': 0, 'end_avail': 180, 'min_dur': 30},
        {'name': 'Matthew', 'location': 'Marina District', 'start_avail': 15, 'end_avail': 315, 'min_dur': 45},
        {'name': 'Joseph', 'location': 'Union Square', 'start_avail': 315, 'end_avail': 585, 'min_dur': 120},
        {'name': 'Ronald', 'location': 'Sunset District', 'start_avail': 420, 'end_avail': 705, 'min_dur': 60},
        {'name': 'Robert', 'location': 'Alamo Square', 'start_avail': 570, 'end_avail': 735, 'min_dur': 120},
        {'name': 'Rebecca', 'location': 'Financial District', 'start_avail': 345, 'end_avail': 435, 'min_dur': 30},
        {'name': 'Elizabeth', 'location': 'Mission District', 'start_avail': 570, 'end_avail': 720, 'min_dur': 120}
    ]
    
    # Create a list of meetings, including virtual start meeting
    meetings = []
    # Virtual meeting0: start at Pacific Heights at time 0
    meetings.append({'name': 'start', 'attended': True, 'start': 0, 'end': 0, 'location': 0})
    
    # Initialize Z3 solver and variables for meetings 1 to 9
    s = Optimize()
    for i in range(1, 10):
        friend = friends[i-1]
        loc_index = locations.index(friend['location'])
        attended = Bool(f'attended_{i}')
        start = Int(f'start_{i}')
        end = start + friend['min_dur']
        meetings.append({'name': friend['name'], 'attended': attended, 'start': start, 'end': end, 'location': loc_index})
    
    # Add constraints for each meeting's availability
    for i in range(1, 10):
        friend = friends[i-1]
        s.add(Implies(meetings[i]['attended'], meetings[i]['start'] >= friend['start_avail']))
        s.add(Implies(meetings[i]['attended'], meetings[i]['end'] <= friend['end_avail']))
    
    # Create before variables for every pair of meetings (including virtual meeting0)
    before = {}
    for i in range(10):
        for j in range(10):
            if i != j:
                before[(i, j)] = Bool(f'before_{i}_{j}')
    
    # Add constraints for every pair of meetings
    for i in range(10):
        for j in range(10):
            if i != j:
                # If both attended, then exactly one of before_i_j or before_j_i is true
                s.add(Implies(And(meetings[i]['attended'], meetings[j]['attended']),
                             Or(before[(i, j)], before[(j, i)])))
                s.add(Implies(And(meetings[i]['attended'], meetings[j]['attended']),
                             Not(And(before[(i, j)], before[(j, i)]))))
                # If i is before j, then start_j >= end_i + travel time from i to j
                s.add(Implies(And(meetings[i]['attended'], meetings[j]['attended'], before[(i, j)]),
                             meetings[j]['start'] >= meetings[i]['end'] + travel_matrix[meetings[i]['location']][meetings[j]['location']]))
    
    # Transitivity constraints for every triple of meetings
    for i in range(10):
        for j in range(10):
            if i == j:
                continue
            for k in range(10):
                if i == k or j == k:
                    continue
                s.add(Implies(And(meetings[i]['attended'], meetings[j]['attended'], meetings[k]['attended'],
                                 before[(i, j)], before[(j, k)]),
                             before[(i, k)]))
    
    # Maximize the number of meetings attended
    total_attended = Sum([If(meetings[i]['attended'], 1, 0) for i in range(1, 10)])
    s.maximize(total_attended)
    
    # Check satisfiability
    if s.check() == sat:
        m = s.model()
        # Collect attended meetings with their start times
        temp_list = []
        for i in range(1, 10):
            if is_true(m.evaluate(meetings[i]['attended'])):
                start_val = m.evaluate(meetings[i]['start']).as_long()
                end_val = start_val + friends[i-1]['min_dur']
                loc = friends[i-1]['location']
                name = friends[i-1]['name']
                temp_list.append((start_val, end_val, loc, name))
        # Sort by start time
        temp_list.sort(key=lambda x: x[0])
        # Convert to itinerary
        itinerary = []
        for (s_val, e_val, loc, name) in temp_list:
            # Convert minutes to time string
            total_minutes_s = s_val
            hours_s = 9 + total_minutes_s // 60
            minutes_s = total_minutes_s % 60
            start_str = f"{hours_s}:{minutes_s:02d}"
            total_minutes_e = e_val
            hours_e = 9 + total_minutes_e // 60
            minutes_e = total_minutes_e % 60
            end_str = f"{hours_e}:{minutes_e:02d}"
            itinerary.append({
                "action": "meet",
                "location": loc,
                "person": name,
                "start_time": start_str,
                "end_time": end_str
            })
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()