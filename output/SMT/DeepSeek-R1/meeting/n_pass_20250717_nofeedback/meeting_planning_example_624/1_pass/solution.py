from z3 import *
import json

def main():
    s = Optimize()
    
    n = 8  # meetings: 0 (dummy) and 1-7 (friends)
    
    # Meet variables: dummy meeting (index0) is always True
    meet = [None] * n
    meet[0] = True
    for i in range(1, n):
        meet[i] = Bool(f"meet_{i}")
    
    # Start and end times (in minutes from 9:00 AM)
    start = [Int(f"start_{i}") for i in range(n)]
    end = [Int(f"end_{i}") for i in range(n)]
    
    # Fix dummy meeting (index0) at Golden Gate Park, start and end at 0 minutes
    s.add(start[0] == 0)
    s.add(end[0] == 0)
    
    # Locations: index corresponds to meeting index
    loc = [0, 1, 2, 3, 4, 5, 6, 7]
    
    # Travel time matrix (8x8)
    travel = [
        [0, 7, 24, 13, 23, 10, 24, 19],
        [7, 0, 23, 6, 19, 5, 19, 17],
        [25, 22, 0, 26, 12, 20, 6, 7],
        [11, 6, 24, 0, 20, 8, 20, 18],
        [23, 19, 8, 22, 0, 17, 3, 7],
        [9, 5, 19, 8, 16, 0, 15, 13],
        [22, 18, 5, 22, 6, 16, 0, 4],
        [21, 17, 7, 21, 9, 15, 5, 0]
    ]
    
    # Availability and duration for each friend (index1 to index7)
    available_start = [0] * n
    available_end = [0] * n
    duration_list = [0] * n
    
    # Carol (index1)
    available_start[1] = 750  # 21:30
    available_end[1] = 810    # 22:30
    duration_list[1] = 60
    
    # Laura (index2)
    available_start[2] = 165  # 11:45
    available_end[2] = 750    # 21:30
    duration_list[2] = 60
    
    # Karen (index3)
    available_start[3] = 0    # 9:00 (since 7:15 is before 9:00)
    available_end[3] = 300    # 14:00
    duration_list[3] = 75
    
    # Elizabeth (index4)
    available_start[4] = 195  # 12:15
    available_end[4] = 750    # 21:30
    duration_list[4] = 75
    
    # Deborah (index5)
    available_start[5] = 180  # 12:00
    available_end[5] = 360    # 15:00
    duration_list[5] = 105
    
    # Jason (index6)
    available_start[6] = 345  # 14:45
    available_end[6] = 600    # 19:00
    duration_list[6] = 90
    
    # Steven (index7)
    available_start[7] = 345  # 14:45
    available_end[7] = 570    # 18:30
    duration_list[7] = 120
    
    # Constraints for each friend meeting
    for i in range(1, n):
        s.add(If(meet[i],
                 And(start[i] >= available_start[i],
                     end[i] == start[i] + duration_list[i],
                     end[i] <= available_end[i]),
                 True))
    
    # Travel constraints between any two meetings
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            s.add(If(And(meet[i], meet[j]),
                     Or(start[j] >= end[i] + travel[loc[i]][loc[j]],
                        start[i] >= end[j] + travel[loc[j]][loc[i]]),
                     True))
    
    # Maximize the number of friends met
    total_meetings = Sum([If(meet[i], 1, 0) for i in range(1, n)])
    s.maximize(total_meetings)
    
    # Check and get the solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        person_map = {
            1: "Carol",
            2: "Laura",
            3: "Karen",
            4: "Elizabeth",
            5: "Deborah",
            6: "Jason",
            7: "Steven"
        }
        
        for i in range(1, n):
            if m.evaluate(meet[i]):
                start_val = m.evaluate(start[i])
                end_val = m.evaluate(end[i])
                if is_int_value(start_val) and is_int_value(end_val):
                    start_min = start_val.as_long()
                    end_min = end_val.as_long()
                    # Convert minutes to HH:MM
                    base_hour = 9
                    hour_start = base_hour + start_min // 60
                    min_start = start_min % 60
                    hour_end = base_hour + end_min // 60
                    min_end = end_min % 60
                    start_str = f"{hour_start:02d}:{min_start:02d}"
                    end_str = f"{hour_end:02d}:{min_end:02d}"
                    itinerary.append({
                        "action": "meet",
                        "person": person_map[i],
                        "start_time": start_str,
                        "end_time": end_str
                    })
        
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x['start_time'])
        print("SOLUTION:")
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

def is_int_value(v):
    return isinstance(v, IntNumRef)

if __name__ == "__main__":
    main()