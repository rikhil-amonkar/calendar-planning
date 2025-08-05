from z3 import *

def main():
    s = Optimize()
    
    # Convert times to minutes from midnight
    start_time = 9 * 60  # 9:00 AM
    sarah_available = (16 * 60, 18 * 60 + 15)  # 4:00 PM - 6:15 PM
    jeffrey_available = (15 * 60, 22 * 60)      # 3:00 PM - 10:00 PM
    brian_available = (16 * 60, 17 * 60 + 30)   # 4:00 PM - 5:30 PM
    
    # Meeting durations
    sarah_duration = 60
    jeffrey_duration = 75
    brian_duration = 75
    
    # Locations: Sunset=0, NorthBeach=1, UnionSquare=2, AlamoSquare=3
    travel_times = [
        [0, 29, 30, 17],  # From Sunset (0)
        [27, 0, 7, 16],   # From NorthBeach (1)
        [26, 10, 0, 15],  # From UnionSquare (2)
        [16, 15, 14, 0]   # From AlamoSquare (3)
    ]
    
    # Meeting slots: 0=none, 1=Sarah, 2=Jeffrey, 3=Brian
    s0 = Int('s0')
    s1 = Int('s1')
    s2 = Int('s2')
    
    # Start times for each slot
    T0 = Int('T0')
    T1 = Int('T1')
    T2 = Int('T2')
    
    # Contiguity constraints
    s.add(Implies(s0 == 0, And(s1 == 0, s2 == 0)))
    s.add(Implies(s1 == 0, s2 == 0))
    
    # Distinct meetings
    s.add(If(s0 != 0, If(s1 != 0, s0 != s1, True), True))
    s.add(If(s0 != 0, If(s2 != 0, s0 != s2, True), True))
    s.add(If(s1 != 0, If(s2 != 0, s1 != s2, True), True))
    
    # Total meetings
    total_meetings = If(s0 != 0, 1, 0) + If(s1 != 0, 1, 0) + If(s2 != 0, 1, 0)
    
    # Location helper functions
    def get_location(meeting):
        return If(meeting == 1, 1, If(meeting == 2, 2, If(meeting == 3, 3, 0)))
    
    # Constraints for slot0
    s.add(Implies(s0 != 0, And(
        T0 >= start_time + travel_times[0][get_location(s0)],
        Or(
            And(s0 == 1, T0 >= sarah_available[0], T0 + sarah_duration <= sarah_available[1]),
            And(s0 == 2, T0 >= jeffrey_available[0], T0 + jeffrey_duration <= jeffrey_available[1]),
            And(s0 == 3, T0 >= brian_available[0], T0 + brian_duration <= brian_available[1])
        )
    )))
    
    # Constraints for slot1
    s.add(Implies(s1 != 0, And(
        s0 != 0,  # Must have previous meeting
        T1 >= T0 + If(s0 == 1, sarah_duration, If(s0 == 2, jeffrey_duration, brian_duration)) + 
                travel_times[get_location(s0)][get_location(s1)],
        Or(
            And(s1 == 1, T1 >= sarah_available[0], T1 + sarah_duration <= sarah_available[1]),
            And(s1 == 2, T1 >= jeffrey_available[0], T1 + jeffrey_duration <= jeffrey_available[1]),
            And(s1 == 3, T1 >= brian_available[0], T1 + brian_duration <= brian_available[1])
        )
    )))
    
    # Constraints for slot2
    s.add(Implies(s2 != 0, And(
        s1 != 0,  # Must have previous meeting
        T2 >= T1 + If(s1 == 1, sarah_duration, If(s1 == 2, jeffrey_duration, brian_duration)) + 
                travel_times[get_location(s1)][get_location(s2)],
        Or(
            And(s2 == 1, T2 >= sarah_available[0], T2 + sarah_duration <= sarah_available[1]),
            And(s2 == 2, T2 >= jeffrey_available[0], T2 + jeffrey_duration <= jeffrey_available[1]),
            And(s2 == 3, T2 >= brian_available[0], T2 + brian_duration <= brian_available[1])
        )
    )))
    
    # Maximize total meetings first
    s.push()
    s.maximize(total_meetings)
    if s.check() != sat:
        print("No solution found")
        return
    m = s.model()
    best_meetings = m.evaluate(total_meetings).as_long()
    s.pop()
    
    # Add constraint for max meetings and minimize start time
    s.add(total_meetings == best_meetings)
    s.minimize(T0)
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        
        def add_meeting(slot_val, start_time_val):
            if slot_val == 1:
                return ("Sarah", start_time_val, start_time_val + sarah_duration)
            elif slot_val == 2:
                return ("Jeffrey", start_time_val, start_time_val + jeffrey_duration)
            elif slot_val == 3:
                return ("Brian", start_time_val, start_time_val + brian_duration)
        
        s0_val = m[s0].as_long()
        if s0_val != 0:
            itinerary.append(add_meeting(s0_val, m[T0].as_long()))
        
        s1_val = m[s1].as_long()
        if s1_val != 0:
            itinerary.append(add_meeting(s1_val, m[T1].as_long()))
        
        s2_val = m[s2].as_long()
        if s2_val != 0:
            itinerary.append(add_meeting(s2_val, m[T2].as_long()))
        
        # Convert times to HH:MM
        result = []
        for person, start_min, end_min in itinerary:
            start_str = f"{start_min // 60:02d}:{start_min % 60:02d}"
            end_str = f"{end_min // 60:02d}:{end_min % 60:02d}"
            result.append({
                "action": "meet",
                "person": person,
                "start_time": start_str,
                "end_time": end_str
            })
        
        # Output solution
        print('SOLUTION:')
        import json
        print(json.dumps({"itinerary": result}))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()