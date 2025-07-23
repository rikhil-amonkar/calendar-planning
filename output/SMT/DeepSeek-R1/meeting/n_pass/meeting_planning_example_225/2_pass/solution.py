from z3 import *

def main():
    # Initialize solver with optimization
    s = Optimize()
    
    # Convert times to minutes from midnight
    start_time = 9 * 60  # 9:00 AM in minutes
    sarah_available_start = 16 * 60  # 4:00 PM
    sarah_available_end = 18 * 60 + 15  # 6:15 PM
    jeffrey_available_start = 15 * 60  # 3:00 PM
    jeffrey_available_end = 22 * 60  # 10:00 PM
    brian_available_start = 16 * 60  # 4:00 PM
    brian_available_end = 17 * 60 + 30  # 5:30 PM
    
    # Duration in minutes
    sarah_duration = 60
    jeffrey_duration = 75
    brian_duration = 75
    
    # Locations: Sunset=0, NorthBeach=1, UnionSquare=2, AlamoSquare=3
    travel_times = [
        [0, 29, 30, 17],  # From Sunset (index 0)
        [27, 0, 7, 16],   # From NorthBeach (index 1)
        [26, 10, 0, 15],  # From UnionSquare (index 2)
        [16, 15, 14, 0]   # From AlamoSquare (index 3)
    ]
    
    # Meeting location indices
    loc_sarah = 1  # NorthBeach
    loc_jeffrey = 2  # UnionSquare
    loc_brian = 3  # AlamoSquare
    
    # Define variables for start times (as integers)
    s_sarah = Int('s_sarah')
    s_jeffrey = Int('s_jeffrey')
    s_brian = Int('s_brian')
    
    # Boolean variables for whether each meeting occurs
    meet_sarah = Bool('meet_sarah')
    meet_jeffrey = Bool('meet_jeffrey')
    meet_brian = Bool('meet_brian')
    
    # Total meetings count
    total_meetings = If(meet_sarah, 1, 0) + If(meet_jeffrey, 1, 0) + If(meet_brian, 1, 0)
    
    # Constraints for meeting durations and availability windows
    c1 = Implies(meet_sarah, And(s_sarah >= sarah_available_start, 
                                 s_sarah + sarah_duration <= sarah_available_end))
    c2 = Implies(meet_jeffrey, And(s_jeffrey >= jeffrey_available_start, 
                                   s_jeffrey + jeffrey_duration <= jeffrey_available_end))
    c3 = Implies(meet_brian, And(s_brian >= brian_available_start, 
                                 s_brian + brian_duration <= brian_available_end))
    
    # Constraints for one meeting (travel from start location)
    c4 = Implies(And(meet_sarah, Not(meet_jeffrey), Not(meet_brian)), 
                 s_sarah >= start_time + travel_times[0][loc_sarah])
    c5 = Implies(And(meet_jeffrey, Not(meet_sarah), Not(meet_brian)), 
                 s_jeffrey >= start_time + travel_times[0][loc_jeffrey])
    c6 = Implies(And(meet_brian, Not(meet_sarah), Not(meet_jeffrey)), 
                 s_brian >= start_time + travel_times[0][loc_brian])
    
    # Constraints for two meetings
    # Sarah and Jeffrey
    c7 = Implies(And(meet_sarah, meet_jeffrey, Not(meet_brian)),
                 Or(
                     # Sarah then Jeffrey
                     And(
                         s_sarah >= start_time + travel_times[0][loc_sarah],
                         s_jeffrey >= s_sarah + sarah_duration + travel_times[loc_sarah][loc_jeffrey]
                     ),
                     # Jeffrey then Sarah
                     And(
                         s_jeffrey >= start_time + travel_times[0][loc_jeffrey],
                         s_sarah >= s_jeffrey + jeffrey_duration + travel_times[loc_jeffrey][loc_sarah]
                     )
                 ))
    
    # Brian and Jeffrey
    c8 = Implies(And(meet_brian, meet_jeffrey, Not(meet_sarah)),
                 And(
                     s_brian >= start_time + travel_times[0][loc_brian],
                     s_jeffrey >= s_brian + brian_duration + travel_times[loc_brian][loc_jeffrey]
                 ))
    
    # Sarah and Brian (infeasible, so set to False)
    c9 = Implies(And(meet_sarah, meet_brian, Not(meet_jeffrey)), False)
    
    # Add all constraints
    s.add(c1, c2, c3, c4, c5, c6, c7, c8, c9)
    
    # Maximize the number of meetings
    s.maximize(total_meetings)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        # Collect meetings that are scheduled
        itinerary = []
        if is_true(m[meet_sarah]):
            start = m[s_sarah].as_long()
            end = start + sarah_duration
            itinerary.append(("Sarah", start, end))
        if is_true(m[meet_jeffrey]):
            start = m[s_jeffrey].as_long()
            end = start + jeffrey_duration
            itinerary.append(("Jeffrey", start, end))
        if is_true(m[meet_brian]):
            start = m[s_brian].as_long()
            end = start + brian_duration
            itinerary.append(("Brian", start, end))
        
        # Sort meetings by start time
        itinerary.sort(key=lambda x: x[1])
        
        # Convert to HH:MM format
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
        
        # Output the solution
        print('SOLUTION:')
        print(json.dumps({"itinerary": result}))
    else:
        print("No solution found")

if __name__ == "__main__":
    import json
    main()