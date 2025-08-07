from z3 import *

def main():
    meetings = [
        {"name": "Margaret", "loc": "Bayview", "start_avail": 30, "end_avail": 270, "duration": 30},
        {"name": "Robert", "loc": "Chinatown", "start_avail": 195, "end_avail": 675, "duration": 15},
        {"name": "Kimberly", "loc": "Marina", "start_avail": 255, "end_avail": 465, "duration": 15},
        {"name": "Rebecca", "loc": "Financial", "start_avail": 255, "end_avail": 465, "duration": 75},
        {"name": "Kenneth", "loc": "Union Square", "start_avail": 630, "end_avail": 735, "duration": 75}
    ]
    
    travel_time_dict = {
        ('Richmond', 'Marina'): 9,
        ('Richmond', 'Chinatown'): 20,
        ('Richmond', 'Financial'): 22,
        ('Richmond', 'Bayview'): 26,
        ('Richmond', 'Union Square'): 21,
        ('Marina', 'Richmond'): 11,
        ('Marina', 'Chinatown'): 16,
        ('Marina', 'Financial'): 17,
        ('Marina', 'Bayview'): 27,
        ('Marina', 'Union Square'): 16,
        ('Chinatown', 'Richmond'): 20,
        ('Chinatown', 'Marina'): 12,
        ('Chinatown', 'Financial'): 5,
        ('Chinatown', 'Bayview'): 22,
        ('Chinatown', 'Union Square'): 7,
        ('Financial', 'Richmond'): 21,
        ('Financial', 'Marina'): 15,
        ('Financial', 'Chinatown'): 5,
        ('Financial', 'Bayview'): 19,
        ('Financial', 'Union Square'): 9,
        ('Bayview', 'Richmond'): 25,
        ('Bayview', 'Marina'): 25,
        ('Bayview', 'Chinatown'): 18,
        ('Bayview', 'Financial'): 19,
        ('Bayview', 'Union Square'): 17,
        ('Union Square', 'Richmond'): 20,
        ('Union Square', 'Marina'): 18,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Financial'): 9,
        ('Union Square', 'Bayview'): 15
    }
    
    locations = [meeting['loc'] for meeting in meetings]
    travel_from_richmond = [travel_time_dict[('Richmond', loc)] for loc in locations]
    
    travel_matrix = []
    for i in range(5):
        row = []
        for j in range(5):
            row.append(travel_time_dict[(locations[i], locations[j])])
        travel_matrix.append(row)
    
    o0, o1, o2, o3, o4 = Ints('o0 o1 o2 o3 o4')
    S = [Int(f'S{i}') for i in range(5)]
    
    s = Solver()
    
    s.add(Distinct(o0, o1, o2, o3, o4))
    for o in [o0, o1, o2, o3, o4]:
        s.add(o >= 0, o < 5)
    
    for i, meeting in enumerate(meetings):
        s.add(S[i] >= meeting['start_avail'])
        s.add(S[i] + meeting['duration'] <= meeting['end_avail'])
    
    def get_end_time(o):
        return If(o == 0, S[0] + meetings[0]['duration'],
                If(o == 1, S[1] + meetings[1]['duration'],
                If(o == 2, S[2] + meetings[2]['duration'],
                If(o == 3, S[3] + meetings[3]['duration'],
                S[4] + meetings[4]['duration']))))
    
    def get_travel_time(oa, ob):
        expr = travel_matrix[0][0]
        for i in range(5):
            for j in range(5):
                expr = If(And(oa == i, ob == j), travel_matrix[i][j], expr)
        return expr
    
    # First meeting constraint
    for j in range(5):
        s.add(Implies(o0 == j, S[j] >= travel_from_richmond[j]))
    
    # Second meeting constraint
    prev_end = get_end_time(o0)
    travel01 = get_travel_time(o0, o1)
    for j in range(5):
        s.add(Implies(o1 == j, S[j] >= prev_end + travel01))
    
    # Third meeting constraint
    prev_end = get_end_time(o1)
    travel12 = get_travel_time(o1, o2)
    for j in range(5):
        s.add(Implies(o2 == j, S[j] >= prev_end + travel12))
    
    # Fourth meeting constraint
    prev_end = get_end_time(o2)
    travel23 = get_travel_time(o2, o3)
    for j in range(5):
        s.add(Implies(o3 == j, S[j] >= prev_end + travel23))
    
    # Fifth meeting constraint
    prev_end = get_end_time(o3)
    travel34 = get_travel_time(o3, o4)
    for j in range(5):
        s.add(Implies(o4 == j, S[j] >= prev_end + travel34))
    
    if s.check() == sat:
        m = s.model()
        schedule = []
        for i in range(5):
            start_val = m.eval(S[i]).as_long()
            hours = 9 + start_val // 60
            minutes = start_val % 60
            start_str = f"{int(hours):02d}:{int(minutes):02d}"
            
            end_val = start_val + meetings[i]['duration']
            hours_end = 9 + end_val // 60
            minutes_end = end_val % 60
            end_str = f"{int(hours_end):02d}:{int(minutes_end):02d}"
            
            schedule.append({
                "person": meetings[i]['name'],
                "start": start_str,
                "end": end_str
            })
        
        schedule.sort(key=lambda x: x['start'])
        itinerary = []
        for meeting in schedule:
            itinerary.append({
                "action": "meet",
                "person": meeting['person'],
                "start_time": meeting['start'],
                "end_time": meeting['end']
            })
        
        print('SOLUTION:')
        print(f'{{"itinerary": {itinerary}}}')
    else:
        print("No solution found")

if __name__ == '__main__':
    main()