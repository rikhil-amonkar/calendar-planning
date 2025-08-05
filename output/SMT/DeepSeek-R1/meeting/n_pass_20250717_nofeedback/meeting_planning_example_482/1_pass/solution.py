from z3 import *
import json

def main():
    meetings = [
        {'name': 'Stephanie', 'loc': 1, 'dur': 90, 'min_start': 495, 'max_end': 825},  # 8:15 AM to 1:45 PM
        {'name': 'Brian', 'loc': 4, 'dur': 120, 'min_start': 735, 'max_end': 960},    # 12:15 PM to 4:00 PM
        {'name': 'Jason', 'loc': 5, 'dur': 60, 'min_start': 510, 'max_end': 1065},    # 8:30 AM to 5:45 PM
        {'name': 'Sandra', 'loc': 2, 'dur': 15, 'min_start': 780, 'max_end': 1170}    # 1:00 PM to 7:30 PM
    ]
    
    travel_times = {
        (0,1): 11, (0,2): 18, (0,4): 17, (0,5): 23,
        (1,0): 12, (1,2): 15, (1,4): 15, (1,5): 22,
        (2,0): 19, (2,1): 13, (2,4): 23, (2,5): 25,
        (4,0): 17, (4,1): 16, (4,2): 23, (4,5): 7,
        (5,0): 22, (5,1): 22, (5,2): 26, (5,4): 7
    }
    
    s = Solver()
    
    order = [Int('order_%d' % i) for i in range(4)]
    for i in range(4):
        s.add(order[i] >= 0, order[i] < 4)
    s.add(Distinct(order))
    
    start_times = [Int('start_%d' % i) for i in range(4)]
    end_times = [Int('end_%d' % i) for i in range(4)]
    
    for i in range(4):
        s.add(end_times[i] == start_times[i] + meetings[i]['dur'])
        s.add(start_times[i] >= meetings[i]['min_start'])
        s.add(end_times[i] <= meetings[i]['max_end'])
    
    first_meeting = order[0]
    s.add(start_times[first_meeting] == 540 + travel_times[(0, meetings[first_meeting]['loc'])])
    
    second_meeting = order[1]
    s.add(start_times[second_meeting] >= end_times[first_meeting] + travel_times[(meetings[first_meeting]['loc'], meetings[second_meeting]['loc'])])
    
    third_meeting = order[2]
    s.add(start_times[third_meeting] >= end_times[second_meeting] + travel_times[(meetings[second_meeting]['loc'], meetings[third_meeting]['loc'])])
    
    fourth_meeting = order[3]
    s.add(start_times[fourth_meeting] >= end_times[third_meeting] + travel_times[(meetings[third_meeting]['loc'], meetings[fourth_meeting]['loc'])])
    
    if s.check() == sat:
        model = s.model()
        order_vals = [model[order[i]].as_long() for i in range(4)]
        start_vals = [model[start_times[i]].as_long() for i in range(4)]
        end_vals = [model[end_times[i]].as_long() for i in range(4)]
        
        itinerary = []
        for idx in order_vals:
            meeting = meetings[idx]
            s_minutes = start_vals[idx]
            e_minutes = end_vals[idx]
            s_hour = s_minutes // 60
            s_minute = s_minutes % 60
            e_hour = e_minutes // 60
            e_minute = e_minutes % 60
            itinerary.append({
                "action": "meet",
                "person": meeting['name'],
                "start_time": f"{s_hour:02d}:{s_minute:02d}",
                "end_time": f"{e_hour:02d}:{e_minute:02d}"
            })
        
        print("SOLUTION:")
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()