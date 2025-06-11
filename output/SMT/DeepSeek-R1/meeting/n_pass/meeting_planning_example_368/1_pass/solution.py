from z3 import *

def min_to_time(total_minutes):
    total_minutes = int(total_minutes)
    hours = total_minutes // 60
    minutes = total_minutes % 60
    if hours == 0:
        return f"12:{minutes:02d} AM"
    elif hours < 12:
        return f"{hours}:{minutes:02d} AM"
    elif hours == 12:
        return f"12:{minutes:02d} PM"
    else:
        return f"{hours-12}:{minutes:02d} PM"

def main():
    # Travel time matrix: [Bayview, Russian Hill, Alamo Square, North Beach, Financial District]
    travel_time = [
        [0, 23, 16, 21, 19],   # from Bayview (index0) to each location
        [23, 0, 15, 5, 11],     # from Russian Hill (index1)
        [16, 13, 0, 15, 17],    # from Alamo Square (index2)
        [22, 4, 16, 0, 8],      # from North Beach (index3)
        [19, 10, 17, 7, 0]      # from Financial District (index4)
    ]
    
    friends = {
        1: {'name': 'Joseph', 'location': 1, 'duration':60, 'start_avail':510, 'end_avail':1155},
        2: {'name': 'Nancy', 'location': 2, 'duration':90, 'start_avail':660, 'end_avail':960},
        3: {'name': 'Jason', 'location': 3, 'duration':15, 'start_avail':1005, 'end_avail':1305},
        4: {'name': 'Jeffrey', 'location': 4, 'duration':45, 'start_avail':630, 'end_avail':945}
    }
    
    s1 = Int('s1')
    s2 = Int('s2')
    s3 = Int('s3')
    s4 = Int('s4')
    
    start1, end1 = Real('start1'), Real('end1')
    start2, end2 = Real('start2'), Real('end2')
    start3, end3 = Real('start3'), Real('end3')
    start4, end4 = Real('start4'), Real('end4')
    
    opt = Optimize()
    
    # Slot constraints: each slot is either -1 (none) or a friend index (1-4)
    opt.add(Or(s1 == -1, s1 == 1, s1 == 2, s1 == 3, s1 == 4))
    opt.add(Or(s2 == -1, s2 == 1, s2 == 2, s2 == 3, s2 == 4))
    opt.add(Or(s3 == -1, s3 == 1, s3 == 2, s3 == 3, s3 == 4))
    opt.add(Or(s4 == -1, s4 == 1, s4 == 2, s4 == 3, s4 == 4))
    
    # If a slot is none, subsequent slots must be none
    opt.add(Implies(s1 == -1, s2 == -1))
    opt.add(Implies(s2 == -1, s3 == -1))
    opt.add(Implies(s3 == -1, s4 == -1))
    
    # Each friend met at most once
    all_slots = [s1, s2, s3, s4]
    for friend in [1, 2, 3, 4]:
        count = Sum([If(s == friend, 1, 0) for s in all_slots])
        opt.add(count <= 1)
    
    # Constraints for slot1
    opt.add(If(s1 != -1,
               And(
                   start1 == 540 + travel_time[0][friends[s1]['location']],
                   end1 == start1 + friends[s1]['duration'],
                   start1 >= friends[s1]['start_avail'],
                   end1 <= friends[s1]['end_avail']
               ),
               True
            ))
    
    # Constraints for slot2
    opt.add(If(s2 != -1,
               And(
                   s1 != -1,
                   start2 == end1 + travel_time[friends[s1]['location']][friends[s2]['location']],
                   end2 == start2 + friends[s2]['duration'],
                   start2 >= friends[s2]['start_avail'],
                   end2 <= friends[s2]['end_avail']
               ),
               True
            ))
    
    # Constraints for slot3
    opt.add(If(s3 != -1,
               And(
                   s2 != -1,
                   start3 == end2 + travel_time[friends[s2]['location']][friends[s3]['location']],
                   end3 == start3 + friends[s3]['duration'],
                   start3 >= friends[s3]['start_avail'],
                   end3 <= friends[s3]['end_avail']
               ),
               True
            ))
    
    # Constraints for slot4
    opt.add(If(s4 != -1,
               And(
                   s3 != -1,
                   start4 == end3 + travel_time[friends[s3]['location']][friends[s4]['location']],
                   end4 == start4 + friends[s4]['duration'],
                   start4 >= friends[s4]['start_avail'],
                   end4 <= friends[s4]['end_avail']
               ),
               True
            ))
    
    num_meetings = Sum([If(s1 != -1, 1, 0), If(s2 != -1, 1, 0), If(s3 != -1, 1, 0), If(s4 != -1, 1, 0)])
    opt.maximize(num_meetings)
    
    if opt.check() == sat:
        m = opt.model()
        slots = [s1, s2, s3, s4]
        start_times = [start1, start2, start3, start4]
        end_times = [end1, end2, end3, end4]
        
        schedule = []
        current_time = 540  # Start at Bayview at 9:00 AM
        
        print("SOLUTION:")
        for i in range(4):
            s_val = m[slots[i]].as_long()
            if s_val == -1:
                continue
            
            friend = friends[s_val]
            start_val = m[start_times[i]]
            end_val = m[end_times[i]]
            
            # Convert Z3 rational to float
            if is_rational_value(start_val):
                start_min = float(start_val.numerator_as_long()) / float(start_val.denominator_as_long())
            elif is_int_value(start_val):
                start_min = start_val.as_long()
            else:
                start_min = 0
                
            if is_rational_value(end_val):
                end_min = float(end_val.numerator_as_long()) / float(end_val.denominator_as_long())
            elif is_int_value(end_val):
                end_min = end_val.as_long()
            else:
                end_min = 0
                
            start_str = min_to_time(start_min)
            end_str = min_to_time(end_min)
            
            travel_from_prev = start_min - current_time
            current_time = end_min
            
            print(f"Travel to {friend['name']} at {friend['location']}: {travel_from_prev} minutes.")
            print(f"Meet {friend['name']} from {start_str} to {end_str} (duration: {friend['duration']} minutes).")
        
        num_met = sum(1 for i in range(4) if m[slots[i]].as_long() != -1)
        print(f"Total friends met: {num_met}")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()