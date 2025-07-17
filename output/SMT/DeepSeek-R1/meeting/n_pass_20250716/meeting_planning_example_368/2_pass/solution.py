from z3 import *

def min_to_time(total_minutes):
    total_minutes = int(round(total_minutes))
    hours = total_minutes // 60
    minutes = total_minutes % 60
    if hours < 12:
        suffix = "AM"
        if hours == 0:
            hours = 12
    else:
        suffix = "PM"
        if hours > 12:
            hours -= 12
    return f"{hours}:{minutes:02d} {suffix}"

def get_travel_time(from_loc, to_loc, matrix):
    expr = matrix[0][0]
    for i in range(5):
        for j in range(5):
            expr = If(And(from_loc == i, to_loc == j), matrix[i][j], expr)
    return expr

def main():
    travel_time = [
        [0, 23, 16, 21, 19],
        [23, 0, 15, 5, 11],
        [16, 13, 0, 15, 17],
        [22, 4, 16, 0, 8],
        [19, 10, 17, 7, 0]
    ]
    
    friends = {
        1: {'name': 'Joseph', 'location': 1, 'duration':60, 'start_avail':510, 'end_avail':1155},
        2: {'name': 'Nancy', 'location': 2, 'duration':90, 'start_avail':660, 'end_avail':960},
        3: {'name': 'Jason', 'location': 3, 'duration':15, 'start_avail':1005, 'end_avail':1305},
        4: {'name': 'Jeffrey', 'location': 4, 'duration':45, 'start_avail':630, 'end_avail':945}
    }
    
    location_names = {
        0: "Bayview",
        1: "Russian Hill",
        2: "Alamo Square",
        3: "North Beach",
        4: "Financial District"
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
    
    opt.add(Or(s1 == -1, s1 == 1, s1 == 2, s1 == 3, s1 == 4))
    opt.add(Or(s2 == -1, s2 == 1, s2 == 2, s2 == 3, s2 == 4))
    opt.add(Or(s3 == -1, s3 == 1, s3 == 2, s3 == 3, s3 == 4))
    opt.add(Or(s4 == -1, s4 == 1, s4 == 2, s4 == 3, s4 == 4))
    
    opt.add(Implies(s1 == -1, s2 == -1))
    opt.add(Implies(s2 == -1, s3 == -1))
    opt.add(Implies(s3 == -1, s4 == -1))
    
    all_slots = [s1, s2, s3, s4]
    for friend in [1, 2, 3, 4]:
        count = Sum([If(s == friend, 1, 0) for s in all_slots])
        opt.add(count <= 1)
    
    loc1 = If(s1 == 1, friends[1]['location'],
              If(s1 == 2, friends[2]['location'],
              If(s1 == 3, friends[3]['location'],
              If(s1 == 4, friends[4]['location'], 0))))
    dur1 = If(s1 == 1, friends[1]['duration'],
             If(s1 == 2, friends[2]['duration'],
             If(s1 == 3, friends[3]['duration'],
             If(s1 == 4, friends[4]['duration'], 0))))
    avail_start1 = If(s1 == 1, friends[1]['start_avail'],
                     If(s1 == 2, friends[2]['start_avail'],
                     If(s1 == 3, friends[3]['start_avail'],
                     If(s1 == 4, friends[4]['start_avail'], 0))))
    avail_end1 = If(s1 == 1, friends[1]['end_avail'],
                   If(s1 == 2, friends[2]['end_avail'],
                   If(s1 == 3, friends[3]['end_avail'],
                   If(s1 == 4, friends[4]['end_avail'], 0)))
    
    opt.add(If(s1 != -1,
               And(
                   start1 == 540 + get_travel_time(0, loc1, travel_time),
                   end1 == start1 + dur1,
                   start1 >= avail_start1,
                   end1 <= avail_end1
               ),
               True
            ))
    
    loc2 = If(s2 == 1, friends[1]['location'],
              If(s2 == 2, friends[2]['location'],
              If(s2 == 3, friends[3]['location'],
              If(s2 == 4, friends[4]['location'], 0))))
    dur2 = If(s2 == 1, friends[1]['duration'],
             If(s2 == 2, friends[2]['duration'],
             If(s2 == 3, friends[3]['duration'],
             If(s2 == 4, friends[4]['duration'], 0))))
    avail_start2 = If(s2 == 1, friends[1]['start_avail'],
                     If(s2 == 2, friends[2]['start_avail'],
                     If(s2 == 3, friends[3]['start_avail'],
                     If(s2 == 4, friends[4]['start_avail'], 0))))
    avail_end2 = If(s2 == 1, friends[1]['end_avail'],
                   If(s2 == 2, friends[2]['end_avail'],
                   If(s2 == 3, friends[3]['end_avail'],
                   If(s2 == 4, friends[4]['end_avail'], 0))))
    
    opt.add(If(s2 != -1,
               And(
                   s1 != -1,
                   start2 == end1 + get_travel_time(loc1, loc2, travel_time),
                   end2 == start2 + dur2,
                   start2 >= avail_start2,
                   end2 <= avail_end2
               ),
               True
            ))
    
    loc3 = If(s3 == 1, friends[1]['location'],
              If(s3 == 2, friends[2]['location'],
              If(s3 == 3, friends[3]['location'],
              If(s3 == 4, friends[4]['location'], 0))))
    dur3 = If(s3 == 1, friends[1]['duration'],
             If(s3 == 2, friends[2]['duration'],
             If(s3 == 3, friends[3]['duration'],
             If(s3 == 4, friends[4]['duration'], 0))))
    avail_start3 = If(s3 == 1, friends[1]['start_avail'],
                     If(s3 == 2, friends[2]['start_avail'],
                     If(s3 == 3, friends[3]['start_avail'],
                     If(s3 == 4, friends[4]['start_avail'], 0))))
    avail_end3 = If(s3 == 1, friends[1]['end_avail'],
                   If(s3 == 2, friends[2]['end_avail'],
                   If(s3 == 3, friends[3]['end_avail'],
                   If(s3 == 4, friends[4]['end_avail'], 0))))
    
    opt.add(If(s3 != -1,
               And(
                   s2 != -1,
                   start3 == end2 + get_travel_time(loc2, loc3, travel_time),
                   end3 == start3 + dur3,
                   start3 >= avail_start3,
                   end3 <= avail_end3
               ),
               True
            ))
    
    loc4 = If(s4 == 1, friends[1]['location'],
              If(s4 == 2, friends[2]['location'],
              If(s4 == 3, friends[3]['location'],
              If(s4 == 4, friends[4]['location'], 0))))
    dur4 = If(s4 == 1, friends[1]['duration'],
             If(s4 == 2, friends[2]['duration'],
             If(s4 == 3, friends[3]['duration'],
             If(s4 == 4, friends[4]['duration'], 0))))
    avail_start4 = If(s4 == 1, friends[1]['start_avail'],
                     If(s4 == 2, friends[2]['start_avail'],
                     If(s4 == 3, friends[3]['start_avail'],
                     If(s4 == 4, friends[4]['start_avail'], 0))))
    avail_end4 = If(s4 == 1, friends[1]['end_avail'],
                   If(s4 == 2, friends[2]['end_avail'],
                   If(s4 == 3, friends[3]['end_avail'],
                   If(s4 == 4, friends[4]['end_avail'], 0))))
    
    opt.add(If(s4 != -1,
               And(
                   s3 != -1,
                   start4 == end3 + get_travel_time(loc3, loc4, travel_time),
                   end4 == start4 + dur4,
                   start4 >= avail_start4,
                   end4 <= avail_end4
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
        
        current_location = 0
        current_time = 540.0
        
        print("SOLUTION:")
        for i in range(4):
            s_val = m[slots[i]].as_long()
            if s_val == -1:
                continue
                
            friend = friends[s_val]
            start_val = m[start_times[i]]
            end_val = m[end_times[i]]
            
            if is_rational_value(start_val):
                start_min = float(start_val.numerator_as_long()) / float(start_val.denominator_as_long())
            elif is_int_value(start_val):
                start_min = float(start_val.as_long())
            else:
                start_min = 0.0
                
            if is_rational_value(end_val):
                end_min = float(end_val.numerator_as_long()) / float(end_val.denominator_as_long())
            elif is_int_value(end_val):
                end_min = float(end_val.as_long())
            else:
                end_min = 0.0
                
            travel_duration = start_min - current_time
            start_str = min_to_time(start_min)
            end_str = min_to_time(end_min)
            
            print(f"Travel from {location_names[current_location]} to {location_names[friend['location']]}: {int(round(travel_duration))} minutes.")
            print(f"Meet {friend['name']} from {start_str} to {end_str} (duration: {friend['duration']} minutes).")
            
            current_location = friend['location']
            current_time = end_min
        
        num_met = sum(1 for i in range(4) if m[slots[i]].as_long() != -1)
        print(f"Total friends met: {num_met}")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()