from z3 import *
import json

def main():
    # Initialize the optimizer
    opt = Optimize()
    
    # Travel times matrix (in minutes)
    # Index: 0=Sunset District, 1=North Beach, 2=Union Square, 3=Alamo Square
    travel_times = [
        [0, 29, 30, 17],
        [27, 0, 7, 16],
        [26, 10, 0, 15],
        [16, 15, 14, 0]
    ]
    
    # Location indices
    sunset_idx = 0
    north_beach_idx = 1
    union_square_idx = 2
    alamo_square_idx = 3
    
    # Convert availability times to minutes since 9:00 AM
    sarah_start = 16*60  # 4:00 PM
    sarah_end = 18*60 + 15  # 6:15 PM
    jeffrey_start = 15*60  # 3:00 PM
    jeffrey_end = 22*60  # 10:00 PM
    brian_start = 16*60  # 4:00 PM
    brian_end = 17*60 + 30  # 5:30 PM
    
    # Minimum meeting durations
    sarah_duration = 60
    jeffrey_duration = 75
    brian_duration = 75
    
    # Decision variables for each meeting
    do_sarah = Bool('do_sarah')
    do_jeffrey = Bool('do_jeffrey')
    do_brian = Bool('do_brian')
    
    # Start time variables (in minutes since 9:00 AM)
    T_sarah = Int('T_sarah')
    T_jeffrey = Int('T_jeffrey')
    T_brian = Int('T_brian')
    
    # Constraints for each meeting if held
    opt.add(Implies(do_sarah, And(T_sarah >= sarah_start, T_sarah + sarah_duration <= sarah_end)))
    opt.add(Implies(do_jeffrey, And(T_jeffrey >= jeffrey_start, T_jeffrey + jeffrey_duration <= jeffrey_end)))
    opt.add(Implies(do_brian, And(T_brian >= brian_start, T_brian + brian_duration <= brian_end)))
    
    # Travel time from Sunset District to first meeting
    opt.add(Implies(do_sarah, T_sarah >= travel_times[sunset_idx][north_beach_idx]))
    opt.add(Implies(do_jeffrey, T_jeffrey >= travel_times[sunset_idx][union_square_idx]))
    opt.add(Implies(do_brian, T_brian >= travel_times[sunset_idx][alamo_square_idx]))
    
    # Pairwise constraints for meetings that are both held
    # Sarah and Jeffrey
    opt.add(Implies(And(do_sarah, do_jeffrey),
                    Or(
                        T_sarah + sarah_duration + travel_times[north_beach_idx][union_square_idx] <= T_jeffrey,
                        T_jeffrey + jeffrey_duration + travel_times[union_square_idx][north_beach_idx] <= T_sarah
                    )))
    
    # Sarah and Brian
    opt.add(Implies(And(do_sarah, do_brian),
                    Or(
                        T_sarah + sarah_duration + travel_times[north_beach_idx][alamo_square_idx] <= T_brian,
                        T_brian + brian_duration + travel_times[alamo_square_idx][north_beach_idx] <= T_sarah
                    )))
    
    # Jeffrey and Brian
    opt.add(Implies(And(do_jeffrey, do_brian),
                    Or(
                        T_jeffrey + jeffrey_duration + travel_times[union_square_idx][alamo_square_idx] <= T_brian,
                        T_brian + brian_duration + travel_times[alamo_square_idx][union_square_idx] <= T_jeffrey
                    )))
    
    # Maximize number of meetings
    opt.maximize(If(do_sarah, 1, 0) + If(do_jeffrey, 1, 0) + If(do_brian, 1, 0))
    
    # Solve the problem
    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        
        # Helper function to convert minutes to time string
        def min_to_time(minutes):
            total_minutes = minutes
            hours = total_minutes // 60
            minutes = total_minutes % 60
            return f"{hours}:{minutes:02d}"
        
        # Collect all scheduled meetings
        meetings = []
        if is_true(m[do_sarah]):
            start = m[T_sarah].as_long()
            meetings.append(("Sarah", "North Beach", start, start + sarah_duration))
        if is_true(m[do_jeffrey]):
            start = m[T_jeffrey].as_long()
            meetings.append(("Jeffrey", "Union Square", start, start + jeffrey_duration))
        if is_true(m[do_brian]):
            start = m[T_brian].as_long()
            meetings.append(("Brian", "Alamo Square", start, start + brian_duration))
        
        # Sort meetings by start time
        meetings.sort(key=lambda x: x[2])
        
        # Build itinerary
        for person, location, start, end in meetings:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": min_to_time(start),
                "end_time": min_to_time(end)
            })
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()