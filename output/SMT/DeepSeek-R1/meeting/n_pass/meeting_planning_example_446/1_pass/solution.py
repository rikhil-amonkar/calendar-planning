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
    
    o0, o1, o2, o3, o4 = Ints('o0 o1 o2 o3 o4')
    S0, S1, S2, S3, S4 = Reals('S0 S1 S2 S3 S4')
    
    s = Solver()
    
    s.add(Distinct(o0, o1, o2, o3, o4))
    for o in [o0, o1, o2, o3, o4]:
        s.add(o >= 0, o < 5)
    
    for i, meeting in enumerate(meetings):
        s.add(eval(f'S{i}') >= meeting['start_avail']
        s.add(eval(f'S{i}') + meeting['duration'] <= meeting['end_avail'])
    
    def build_travel_start(order_var):
        cases = []
        for i in range(5):
            tt = travel_time_dict[('Richmond', meetings[i]['loc'])]
            cases.append((order_var == i, tt))
        return If(cases[0][0], cases[0][1],
                If(cases[1][0], cases[1][1],
                If(cases[2][0], cases[2][1],
                If(cases[3][0], cases[3][1],
                If(cases[4][0], cases[4][1], 0)))))
    
    def build_travel_between(order_var1, order_var2):
        cases = []
        for i in range(5):
            for j in range(5):
                tt = travel_time_dict[(meetings[i]['loc'], meetings[j]['loc'])]
                cases.append((And(order_var1 == i, order_var2 == j), tt))
        expr = cases[0][1]
        for i in range(1, len(cases)):
            expr = If(cases[i][0], cases[i][1], expr)
        return expr
    
    def build_end_time_expr(order_var):
        return If(order_var == 0, S0 + meetings[0]['duration'],
                If(order_var == 1, S1 + meetings[1]['duration'],
                If(order_var == 2, S2 + meetings[2]['duration'],
                If(order_var == 3, S3 + meetings[3]['duration'],
                If(order_var == 4, S4 + meetings[4]['duration'], 0)))))
    
    def build_start_constraint(order_var, required_start):
        return If(order_var == 0, S0 >= required_start,
                If(order_var == 1, S1 >= required_start,
                If(order_var == 2, S2 >= required_start,
                If(order_var == 3, S3 >= required_start,
                If(order_var == 4, S4 >= required_start, False)))))
    
    T0 = build_travel_start(o0)
    s.add(build_start_constraint(o0, T0))
    
    T1 = build_travel_between(o0, o1)
    E0 = build_end_time_expr(o0)
    s.add(build_start_constraint(o1, E0 + T1))
    
    T2 = build_travel_between(o1, o2)
    E1 = build_end_time_expr(o1)
    s.add(build_start_constraint(o2, E1 + T2))
    
    T3 = build_travel_between(o2, o3)
    E2 = build_end_time_expr(o2)
    s.add(build_start_constraint(o3, E2 + T3))
    
    T4 = build_travel_between(o3, o4)
    E3 = build_end_time_expr(o3)
    s.add(build_start_constraint(o4, E3 + T4))
    
    if s.check() == sat:
        m = s.model()
        start_times = []
        for i in range(5):
            start_val = m.eval(eval(f'S{i}'))
            if is_algebraic_value(start_val):
                start_val = start_val.approx().as_long()
            else:
                start_val = start_val.as_long()
            start_times.append(start_val)
        
        meeting_schedule = []
        for i in range(5):
            start_minutes = start_times[i]
            hours = 9 + start_minutes // 60
            minutes = start_minutes % 60
            start_str = f"{int(hours):02d}:{int(minutes):02d}"
            
            end_minutes = start_minutes + meetings[i]['duration']
            hours_end = 9 + end_minutes // 60
            minutes_end = end_minutes % 60
            end_str = f"{int(hours_end):02d}:{int(minutes_end):02d}"
            
            meeting_schedule.append({
                "person": meetings[i]["name"],
                "start": start_str,
                "end": end_str
            })
        
        meeting_schedule.sort(key=lambda x: x["start"])
        itinerary = []
        for meeting in meeting_schedule:
            itinerary.append({
                "action": "meet",
                "person": meeting["person"],
                "start_time": meeting["start"],
                "end_time": meeting["end"]
            })
        
        print('SOLUTION:')
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == '__main__':
    main()