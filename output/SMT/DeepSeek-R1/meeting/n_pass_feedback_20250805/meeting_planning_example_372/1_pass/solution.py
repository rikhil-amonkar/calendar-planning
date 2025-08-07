from z3 import *

def main():
    # Travel time matrix (5x5) in minutes. Rows and columns: 0=Sunset, 1=Alamo, 2=Russian, 3=Golden, 4=Mission
    T = [
        [0, 17, 24, 11, 24],   # From Sunset (0)
        [16, 0, 13, 9, 10],    # From Alamo (1)
        [23, 15, 0, 21, 16],   # From Russian (2)
        [10, 10, 19, 0, 17],   # From Golden (3)
        [24, 11, 15, 17, 0]    # From Mission (4)
    ]
    
    # Initialize Z3 solver with optimization
    opt = Optimize()
    
    # Meet booleans for Charles, Margaret, Daniel, Stephanie
    meet1 = Bool('meet1')  # Charles
    meet2 = Bool('meet2')  # Margaret
    meet3 = Bool('meet3')  # Daniel
    meet4 = Bool('meet4')  # Stephanie
    meet = [None, meet1, meet2, meet3, meet4]  # Index 0 unused
    
    # Start and end times for events 0 (start) and 1-4 (meetings)
    start0 = 540  # 9:00 AM in minutes
    end0 = 540
    start1 = Int('start1')
    start2 = Int('start2')
    start3 = Int('start3')
    start4 = Int('start4')
    start = [start0, start1, start2, start3, start4]
    
    # Durations: event0=0, Charles=90, Margaret=30, Daniel=15, Stephanie=90
    durations = [0, 90, 30, 15, 90]
    end1 = start1 + durations[1]
    end2 = start2 + durations[2]
    end3 = start3 + durations[3]
    end4 = start4 + durations[4]
    end = [end0, end1, end2, end3, end4]
    
    # Constraints for each meeting if scheduled
    # Charles (event1): available 18:00 (1080) to 20:45 (1245)
    opt.add(Implies(meet1, And(start1 >= 1080, end1 <= 1245)))
    # Margaret (event2): available 9:00 (540) to 16:00 (960)
    opt.add(Implies(meet2, And(start2 >= 540, end2 <= 960)))
    # Daniel (event3): available 8:00 (480) to 13:30 (810)
    opt.add(Implies(meet3, And(start3 >= 480, end3 <= 810)))
    # Stephanie (event4): available 20:30 (1230) to 22:00 (1320)
    opt.add(Implies(meet4, And(start4 >= 1230, end4 <= 1320)))
    
    # Constraints for travel between any two events (i < j) if both are active
    for i in range(5):
        for j in range(i+1, 5):
            # Check if both events are active
            active_i = True if i == 0 else meet[i]
            active_j = True if j == 0 else meet[j]
            b = Bool(f'b_{i}_{j}')
            # Order constraint: if i before j, then end_i + travel time <= start_j, else end_j + travel time <= start_i
            opt.add(Implies(And(active_i, active_j),
                Or(
                    And(b, start[i] < start[j], end[i] + T[i][j] <= start[j]),
                    And(Not(b), start[j] < start[i], end[j] + T[j][i] <= start[i])
                )
            ))
    
    # Maximize the number of meetings
    total_meetings = Sum([If(meet1, 1, 0), If(meet2, 1, 0), If(meet3, 1, 0), If(meet4, 1, 0)])
    opt.maximize(total_meetings)
    
    # Solve the problem
    if opt.check() == sat:
        m = opt.model()
        scheduled_meetings = []
        # Collect scheduled meetings
        friends = [None, "Charles", "Margaret", "Daniel", "Stephanie"]
        for idx in [1, 2, 3, 4]:
            if m.evaluate(meet[idx]):
                start_time_min = m.evaluate(start[idx]).as_long()
                end_time_min = start_time_min + durations[idx]
                # Convert to HH:MM
                start_hour = start_time_min // 60
                start_minute = start_time_min % 60
                end_hour = end_time_min // 60
                end_minute = end_time_min % 60
                start_str = f"{start_hour:02d}:{start_minute:02d}"
                end_str = f"{end_hour:02d}:{end_minute:02d}"
                scheduled_meetings.append({
                    "person": friends[idx],
                    "start_time": start_str,
                    "end_time": end_str
                })
        # Sort by start time
        scheduled_meetings.sort(key=lambda x: x['start_time'])
        itinerary = [{"action": "meet", "person": mt["person"], "start_time": mt["start_time"], "end_time": mt["end_time"]} for mt in scheduled_meetings]
        result = {"itinerary": itinerary}
        print(f"SOLUTION: {result}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()