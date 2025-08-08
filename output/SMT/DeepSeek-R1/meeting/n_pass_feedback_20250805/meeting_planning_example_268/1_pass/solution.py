from z3 import *
import json

def main():
    # Meeting data: name, available start, available end, minimum time, location index
    meetings = [
        {'name': 'Timothy', 'avail_start': 12*60, 'avail_end': 16*60+15, 'min_time': 105, 'loc': 1},
        {'name': 'Joseph', 'avail_start': 16*60+45, 'avail_end': 21*60+30, 'min_time': 60, 'loc': 3},
        {'name': 'Mark', 'avail_start': 18*60+45, 'avail_end': 21*60, 'min_time': 60, 'loc': 2}
    ]
    
    # Travel time function between locations (0: GG, 1: AS, 2: P, 3: RH)
    def travel_time(from_loc, to_loc):
        return If(And(from_loc == 0, to_loc == 1), 10,
               If(And(from_loc == 0, to_loc == 2), 11,
               If(And(from_loc == 0, to_loc == 3), 19,
               If(And(from_loc == 1, to_loc == 0), 9,
               If(And(from_loc == 1, to_loc == 2), 18,
               If(And(from_loc == 1, to_loc == 3), 13,
               If(And(from_loc == 2, to_loc == 0), 12,
               If(And(from_loc == 2, to_loc == 1), 18,
               If(And(from_loc == 2, to_loc == 3), 14,
               If(And(from_loc == 3, to_loc == 0), 21,
               If(And(from_loc == 3, to_loc == 1), 15,
               If(And(from_loc == 3, to_loc == 2), 14,
               0  # default (should not occur)
               ))))))))))))
    
    # Z3 variables for meeting order and start times
    first = Int('first')
    second = Int('second')
    third = Int('third')
    s0 = Int('s0')
    s1 = Int('s1')
    s2 = Int('s2')
    
    s = Solver()
    
    # Permutation constraints: distinct and in range [0,2]
    s.add(first >= 0, first <= 2)
    s.add(second >= 0, second <= 2)
    s.add(third >= 0, third <= 2)
    s.add(Distinct(first, second, third))
    
    # Start location: Golden Gate Park (0) at 9:00 AM (540 minutes)
    start_time = 9 * 60
    
    # Z3 arrays for meeting attributes
    avail_start_arr = Array('avail_start_arr', IntSort(), IntSort())
    avail_end_arr = Array('avail_end_arr', IntSort(), IntSort())
    min_time_arr = Array('min_time_arr', IntSort(), IntSort())
    loc_arr = Array('loc_arr', IntSort(), IntSort())
    
    for i in range(3):
        s.add(avail_start_arr[i] == meetings[i]['avail_start'])
        s.add(avail_end_arr[i] == meetings[i]['avail_end'])
        s.add(min_time_arr[i] == meetings[i]['min_time'])
        s.add(loc_arr[i] == meetings[i]['loc'])
    
    # First meeting constraints
    loc0 = loc_arr[first]
    s.add(s0 >= start_time + travel_time(0, loc0))
    s.add(s0 >= avail_start_arr[first])
    s.add(s0 + min_time_arr[first] <= avail_end_arr[first])
    
    # Second meeting constraints
    loc1 = loc_arr[second]
    s.add(s1 >= s0 + min_time_arr[first] + travel_time(loc0, loc1))
    s.add(s1 >= avail_start_arr[second])
    s.add(s1 + min_time_arr[second] <= avail_end_arr[second])
    
    # Third meeting constraints
    loc2 = loc_arr[third]
    s.add(s2 >= s1 + min_time_arr[second] + travel_time(loc1, loc2))
    s.add(s2 >= avail_start_arr[third])
    s.add(s2 + min_time_arr[third] <= avail_end_arr[third])
    
    # Check for solution
    if s.check() == sat:
        m = s.model()
        first_val = m[first].as_long()
        second_val = m[second].as_long()
        third_val = m[third].as_long()
        s0_val = m[s0].as_long()
        s1_val = m[s1].as_long()
        s2_val = m[s2].as_long()
        
        # Helper function to convert minutes to time string
        def to_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"
        
        # Build itinerary in chronological order
        itinerary = [
            {
                'action': 'meet',
                'person': meetings[first_val]['name'],
                'start_time': to_time(s0_val),
                'end_time': to_time(s0_val + meetings[first_val]['min_time'])
            },
            {
                'action': 'meet',
                'person': meetings[second_val]['name'],
                'start_time': to_time(s1_val),
                'end_time': to_time(s1_val + meetings[second_val]['min_time'])
            },
            {
                'action': 'meet',
                'person': meetings[third_val]['name'],
                'start_time': to_time(s2_val),
                'end_time': to_time(s2_val + meetings[third_val]['min_time'])
            }
        ]
        
        # Output solution
        print("SOLUTION:")
        print(json.dumps({'itinerary': itinerary}))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()