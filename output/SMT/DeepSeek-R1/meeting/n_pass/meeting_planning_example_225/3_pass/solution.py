from z3 import *

def main():
    # Initialize optimizer
    s = Optimize()
    
    # Convert times to minutes from midnight
    start_time = 9 * 60  # 9:00 AM
    sarah_available_start = 16 * 60  # 4:00 PM
    sarah_available_end = 18 * 60 + 15  # 6:15 PM
    jeffrey_available_start = 15 * 60  # 3:00 PM
    jeffrey_available_end = 22 * 60  # 10:00 PM
    brian_available_start = 16 * 60  # 4:00 PM
    brian_available_end = 17 * 60 + 30  # 5:30 PM
    
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
    
    # Meeting codes: 0=none, 1=Sarah, 2=Jeffrey, 3=Brian
    s0 = Int('s0')
    s1 = Int('s1')
    s2 = Int('s2')
    
    # Start times for each slot
    T0 = Int('T0')
    T1 = Int('T1')
    T2 = Int('T2')
    
    # Contiguity constraints
    c_contiguity = And(
        Implies(s0 == 0, And(s1 == 0, s2 == 0)),
        Implies(s1 == 0, s2 == 0)
    )
    
    # Distinct meetings (non-zero)
    c_distinct = And(
        Implies(And(s0 != 0, s1 != 0), s0 != s1),
        Implies(And(s0 != 0, s2 != 0), s0 != s2),
        Implies(And(s1 != 0, s2 != 0), s1 != s2)
    )
    
    # Total meetings
    total_meetings = If(s0 != 0, 1, 0) + If(s1 != 0, 1, 0) + If(s2 != 0, 1, 0)
    
    # Constraints for each slot
    c_slot0 = []
    # If slot0 has a meeting, set constraints based on meeting type
    c_slot0.append(Implies(s0 == 1, 
                          And(T0 >= sarah_available_start,
                              T0 + sarah_duration <= sarah_available_end,
                              T0 >= start_time + travel_times[0][1])))
    c_slot0.append(Implies(s0 == 2,
                          And(T0 >= jeffrey_available_start,
                              T0 + jeffrey_duration <= jeffrey_available_end,
                              T0 >= start_time + travel_times[0][2])))
    c_slot0.append(Implies(s0 == 3,
                          And(T0 >= brian_available_start,
                              T0 + brian_duration <= brian_available_end,
                              T0 >= start_time + travel_times[0][3])))
    c_slot0 = And(c_slot0)
    
    c_slot1 = []
    # If slot1 has a meeting, set constraints based on meeting type and travel from slot0
    c_slot1.append(Implies(s1 != 0, 
        Or(
            And(s0 == 1, 
                Or(
                    And(s1 == 2, T1 >= T0 + sarah_duration + travel_times[1][2]),
                    And(s1 == 3, T1 >= T0 + sarah_duration + travel_times[1][3])
                )),
            And(s0 == 2,
                Or(
                    And(s1 == 1, T1 >= T0 + jeffrey_duration + travel_times[2][1]),
                    And(s1 == 3, T1 >= T0 + jeffrey_duration + travel_times[2][3])
                )),
            And(s0 == 3,
                Or(
                    And(s1 == 1, T1 >= T0 + brian_duration + travel_times[3][1]),
                    And(s1 == 2, T1 >= T0 + brian_duration + travel_times[3][2])
                ))
        )))
    # Add availability constraints for slot1 meetings
    c_slot1.append(Implies(s1 == 1, 
                          And(T1 >= sarah_available_start,
                              T1 + sarah_duration <= sarah_available_end)))
    c_slot1.append(Implies(s1 == 2,
                          And(T1 >= jeffrey_available_start,
                              T1 + jeffrey_duration <= jeffrey_available_end)))
    c_slot1.append(Implies(s1 == 3,
                          And(T1 >= brian_available_start,
                              T1 + brian_duration <= brian_available_end)))
    c_slot1 = And(c_slot1)
    
    c_slot2 = []
    # If slot2 has a meeting, set constraints based on meeting type and travel from slot1
    c_slot2.append(Implies(s2 != 0, 
        Or(
            And(s1 == 1, 
                Or(
                    And(s2 == 2, T2 >= T1 + sarah_duration + travel_times[1][2]),
                    And(s2 == 3, T2 >= T1 + sarah_duration + travel_times[1][3])
                )),
            And(s1 == 2,
                Or(
                    And(s2 == 1, T2 >= T1 + jeffrey_duration + travel_times[2][1]),
                    And(s2 == 3, T2 >= T1 + jeffrey_duration + travel_times[2][3])
                )),
            And(s1 == 3,
                Or(
                    And(s2 == 1, T2 >= T1 + brian_duration + travel_times[3][1]),
                    And(s2 == 2, T2 >= T1 + brian_duration + travel_times[3][2])
                ))
        )))
    # Add availability constraints for slot2 meetings
    c_slot2.append(Implies(s2 == 1, 
                          And(T2 >= sarah_available_start,
                              T2 + sarah_duration <= sarah_available_end)))
    c_slot2.append(Implies(s2 == 2,
                          And(T2 >= jeffrey_available_start,
                              T2 + jeffrey_duration <= jeffrey_available_end)))
    c_slot2.append(Implies(s2 == 3,
                          And(T2 >= brian_available_start,
                              T2 + brian_duration <= brian_available_end)))
    c_slot2 = And(c_slot2)
    
    # Add all constraints
    s.add(c_contiguity, c_distinct, c_slot0, c_slot1, c_slot2)
    
    # Define domain for s0, s1, s2
    s.add(Or(s0 == 0, s0 == 1, s0 == 2, s0 == 3))
    s.add(Or(s1 == 0, s1 == 1, s1 == 2, s1 == 3))
    s.add(Or(s2 == 0, s2 == 1, s2 == 2, s2 == 3))
    
    # Maximize total meetings
    s.maximize(total_meetings)
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        s0_val = m[s0].as_long()
        s1_val = m[s1].as_long()
        s2_val = m[s2].as_long()
        T0_val = m[T0].as_long()
        T1_val = m[T1].as_long() if s1_val != 0 else None
        T2_val = m[T2].as_long() if s2_val != 0 else None
        
        def add_meeting(slot_val, start_time_val, duration):
            if slot_val == 1:
                return ("Sarah", start_time_val, start_time_val + duration)
            elif slot_val == 2:
                return ("Jeffrey", start_time_val, start_time_val + duration)
            elif slot_val == 3:
                return ("Brian", start_time_val, start_time_val + duration)
        
        if s0_val != 0:
            itinerary.append(add_meeting(s0_val, T0_val, 
                sarah_duration if s0_val==1 else jeffrey_duration if s0_val==2 else brian_duration))
        if s1_val != 0:
            itinerary.append(add_meeting(s1_val, T1_val, 
                sarah_duration if s1_val==1 else jeffrey_duration if s1_val==2 else brian_duration))
        if s2_val != 0:
            itinerary.append(add_meeting(s2_val, T2_val, 
                sarah_duration if s2_val==1 else jeffrey_duration if s2_val==2 else brian_duration))
        
        # Convert times to HH:MM
        result = []
        for person, start_min, end_min in itinerary:
            start_h = start_min // 60
            start_m = start_min % 60
            end_h = end_min // 60
            end_m = end_min % 60
            start_str = f"{start_h:02d}:{start_m:02d}"
            end_str = f"{end_h:02d}:{end_m:02d}"
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