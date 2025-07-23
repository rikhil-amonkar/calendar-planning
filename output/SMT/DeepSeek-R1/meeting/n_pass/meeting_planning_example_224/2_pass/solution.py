from z3 import *
import json

def main():
    meetings = [
        {"name": "Melissa", "location": "GG", "min_duration": 15, "available_start": -30, "available_end": 660},
        {"name": "Emily", "location": "Rich", "min_duration": 120, "available_start": 465, "available_end": 780},
        {"name": "Nancy", "location": "Pres", "min_duration": 105, "available_start": 645, "available_end": 780}
    ]
    
    fw_travel = {
        "GG": 25,
        "Rich": 18,
        "Pres": 17
    }
    
    travel_times = {
        ("GG", "Rich"): 7,
        ("GG", "Pres"): 11,
        ("Rich", "GG"): 9,
        ("Rich", "Pres"): 7,
        ("Pres", "GG"): 12,
        ("Pres", "Rich"): 7
    }
    
    s = [Int(f's{i}') for i in range(3)]
    first = Int('first')
    second = Int('second')
    third = Int('third')
    
    solver = Solver()
    
    solver.add(Distinct(first, second, third))
    solver.add(first >= 0, first <= 2)
    solver.add(second >= 0, second <= 2)
    solver.add(third >= 0, third <= 2)
    
    for i in range(3):
        solver.add(s[i] >= 0)
    
    travel_time0 = If(first == 0, fw_travel["GG"],
                      If(first == 1, fw_travel["Rich"],
                      fw_travel["Pres"]))
    
    solver.add(If(first == 0, s[0] >= travel_time0,
                  If(first == 1, s[1] >= travel_time0,
                  s[2] >= travel_time0)))
    
    def get_travel_time(idx1, idx2):
        loc1 = meetings[idx1]['location']
        loc2 = meetings[idx2]['location']
        return travel_times.get((loc1, loc2), 0)
    
    travel_time1 = If(And(first == 0, second == 1), get_travel_time(0, 1),
                      If(And(first == 0, second == 2), get_travel_time(0, 2),
                      If(And(first == 1, second == 0), get_travel_time(1, 0),
                      If(And(first == 1, second == 2), get_travel_time(1, 2),
                      If(And(first == 2, second == 0), get_travel_time(2, 0),
                      If(And(first == 2, second == 1), get_travel_time(2, 1), 0))))))
    
    min_duration_first = If(first == 0, meetings[0]['min_duration'],
                            If(first == 1, meetings[1]['min_duration'],
                            meetings[2]['min_duration']))
    
    solver.add(If(second == 0, 
                  s[0] >= If(first == 0, s[0] + min_duration_first,
                              If(first == 1, s[1] + min_duration_first,
                              s[2] + min_duration_first)) + travel_time1,
                If(second == 1,
                  s[1] >= If(first == 0, s[0] + min_duration_first,
                              If(first == 1, s[1] + min_duration_first,
                              s[2] + min_duration_first)) + travel_time1,
                  s[2] >= If(first == 0, s[0] + min_duration_first,
                              If(first == 1, s[1] + min_duration_first,
                              s[2] + min_duration_first)) + travel_time1)))
    
    travel_time2 = If(And(second == 0, third == 1), get_travel_time(0, 1),
                      If(And(second == 0, third == 2), get_travel_time(0, 2),
                      If(And(second == 1, third == 0), get_travel_time(1, 0),
                      If(And(second == 1, third == 2), get_travel_time(1, 2),
                      If(And(second == 2, third == 0), get_travel_time(2, 0),
                      If(And(second == 2, third == 1), get_travel_time(2, 1), 0))))))
    
    min_duration_second = If(second == 0, meetings[0]['min_duration'],
                             If(second == 1, meetings[1]['min_duration'],
                             meetings[2]['min_duration']))
    
    solver.add(If(third == 0, 
                  s[0] >= If(second == 0, s[0] + min_duration_second,
                              If(second == 1, s[1] + min_duration_second,
                              s[2] + min_duration_second)) + travel_time2,
                If(third == 1,
                  s[1] >= If(second == 0, s[0] + min_duration_second,
                              If(second == 1, s[1] + min_duration_second,
                              s[2] + min_duration_second)) + travel_time2,
                  s[2] >= If(second == 0, s[0] + min_duration_second,
                              If(second == 1, s[1] + min_duration_second,
                              s[2] + min_duration_second)) + travel_time2)))
    
    solver.add(s[0] >= meetings[0]['available_start'])
    solver.add(s[0] + meetings[0]['min_duration'] <= meetings[0]['available_end'])
    
    solver.add(s[1] >= meetings[1]['available_start'])
    solver.add(s[1] + meetings[1]['min_duration'] <= meetings[1]['available_end'])
    
    solver.add(s[2] >= meetings[2]['available_start'])
    solver.add(s[2] + meetings[2]['min_duration'] <= meetings[2]['available_end'])
    
    if solver.check() == sat:
        model = solver.model()
        s0_val = model.evaluate(s[0]).as_long()
        s1_val = model.evaluate(s[1]).as_long()
        s2_val = model.evaluate(s[2]).as_long()
        
        def min_to_time(minutes):
            base_minutes = 9 * 60
            total_minutes_since_midnight = base_minutes + minutes
            hours = total_minutes_since_midnight // 60
            mins = total_minutes_since_midnight % 60
            return f"{hours:02d}:{mins:02d}"
        
        meetings_list = [
            {"person": "Melissa", "start": s0_val, "end": s0_val + meetings[0]['min_duration']},
            {"person": "Emily", "start": s1_val, "end": s1_val + meetings[1]['min_duration']},
            {"person": "Nancy", "start": s2_val, "end": s2_val + meetings[2]['min_duration']}
        ]
        
        sorted_meetings = sorted(meetings_list, key=lambda x: x['start'])
        
        itinerary = []
        for m in sorted_meetings:
            itinerary.append({
                "action": "meet",
                "person": m['person'],
                "start_time": min_to_time(m['start']),
                "end_time": min_to_time(m['end'])
            })
        
        print('SOLUTION:')
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()