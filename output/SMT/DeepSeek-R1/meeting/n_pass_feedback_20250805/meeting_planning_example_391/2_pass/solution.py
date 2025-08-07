from z3 import *

def min_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def main():
    friends_list = ['Kevin', 'Kimberly', 'Joseph', 'Thomas']
    available_start = [8*60+15, 8*60+45, 18*60+30, 19*60+0]
    available_end = [21*60+30, 12*60+30, 19*60+15, 21*60+45]
    min_time_list = [75, 30, 45, 45]
    
    travel_from_sunset = [17, 24, 16, 30]
    
    travel_between = [
        [0, 13, 18, 17],
        [15, 0, 14, 11],
        [18, 14, 0, 23],
        [17, 10, 22, 0]
    ]
    
    s = Solver()
    
    friend0 = Int('friend0')
    friend1 = Int('friend1')
    friend2 = Int('friend2')
    friend3 = Int('friend3')
    s.add(friend0 >= 0, friend0 < 4)
    s.add(friend1 >= 0, friend1 < 4)
    s.add(friend2 >= 0, friend2 < 4)
    s.add(friend3 >= 0, friend3 < 4)
    s.add(Distinct(friend0, friend1, friend2, friend3))
    
    travel_time0 = Int('travel_time0')
    s.add(travel_time0 == If(friend0 == 0, travel_from_sunset[0],
                          If(friend0 == 1, travel_from_sunset[1],
                          If(friend0 == 2, travel_from_sunset[2],
                                          travel_from_sunset[3]))))
    
    travel_time1 = Int('travel_time1')
    s.add(travel_time1 == If(And(friend0 == 0, friend1 == 1), travel_between[0][1],
                          If(And(friend0 == 0, friend1 == 2), travel_between[0][2],
                          If(And(friend0 == 0, friend1 == 3), travel_between[0][3],
                          If(And(friend0 == 1, friend1 == 0), travel_between[1][0],
                          If(And(friend0 == 1, friend1 == 2), travel_between[1][2],
                          If(And(friend0 == 1, friend1 == 3), travel_between[1][3],
                          If(And(friend0 == 2, friend1 == 0), travel_between[2][0],
                          If(And(friend0 == 2, friend1 == 1), travel_between[2][1],
                          If(And(friend0 == 2, friend1 == 3), travel_between[2][3],
                          If(And(friend0 == 3, friend1 == 0), travel_between[3][0],
                          If(And(friend0 == 3, friend1 == 1), travel_between[3][1],
                          If(And(friend0 == 3, friend1 == 2), travel_between[3][2],
                          0)))))))))))))
    
    travel_time2 = Int('travel_time2')
    s.add(travel_time2 == If(And(friend1 == 0, friend2 == 1), travel_between[0][1],
                          If(And(friend1 == 0, friend2 == 2), travel_between[0][2],
                          If(And(friend1 == 0, friend2 == 3), travel_between[0][3],
                          If(And(friend1 == 1, friend2 == 0), travel_between[1][0],
                          If(And(friend1 == 1, friend2 == 2), travel_between[1][2],
                          If(And(friend1 == 1, friend2 == 3), travel_between[1][3],
                          If(And(friend1 == 2, friend2 == 0), travel_between[2][0],
                          If(And(friend1 == 2, friend2 == 1), travel_between[2][1],
                          If(And(friend1 == 2, friend2 == 3), travel_between[2][3],
                          If(And(friend1 == 3, friend2 == 0), travel_between[3][0],
                          If(And(friend1 == 3, friend2 == 1), travel_between[3][1],
                          If(And(friend1 == 3, friend2 == 2), travel_between[3][2],
                          0)))))))))))))
    
    travel_time3 = Int('travel_time3')
    s.add(travel_time3 == If(And(friend2 == 0, friend3 == 1), travel_between[0][1],
                          If(And(friend2 == 0, friend3 == 2), travel_between[0][2],
                          If(And(friend2 == 0, friend3 == 3), travel_between[0][3],
                          If(And(friend2 == 1, friend3 == 0), travel_between[1][0],
                          If(And(friend2 == 1, friend3 == 2), travel_between[1][2],
                          If(And(friend2 == 1, friend3 == 3), travel_between[1][3],
                          If(And(friend2 == 2, friend3 == 0), travel_between[2][0],
                          If(And(friend2 == 2, friend3 == 1), travel_between[2][1],
                          If(And(friend2 == 2, friend3 == 3), travel_between[2][3],
                          If(And(friend2 == 3, friend3 == 0), travel_between[3][0],
                          If(And(friend2 == 3, friend3 == 1), travel_between[3][1],
                          If(And(friend2 == 3, friend3 == 2), travel_between[3][2],
                          0)))))))))))))
    
    start0 = Int('start0')
    end0 = Int('end0')
    start1 = Int('start1')
    end1 = Int('end1')
    start2 = Int('start2')
    end2 = Int('end2')
    start3 = Int('start3')
    end3 = Int('end3')
    
    available_start0 = If(friend0 == 0, available_start[0],
                      If(friend0 == 1, available_start[1],
                      If(friend0 == 2, available_start[2],
                         available_start[3])))
    available_end0 = If(friend0 == 0, available_end[0],
                    If(friend0 == 1, available_end[1],
                    If(friend0 == 2, available_end[2],
                       available_end[3])))
    min_time0 = If(friend0 == 0, min_time_list[0],
                If(friend0 == 1, min_time_list[1],
                If(friend0 == 2, min_time_list[2],
                   min_time_list[3])))
    
    available_start1 = If(friend1 == 0, available_start[0],
                      If(friend1 == 1, available_start[1],
                      If(friend1 == 2, available_start[2],
                         available_start[3])))
    available_end1 = If(friend1 == 0, available_end[0],
                    If(friend1 == 1, available_end[1],
                    If(friend1 == 2, available_end[2],
                       available_end[3])))
    min_time1 = If(friend1 == 0, min_time_list[0],
                If(friend1 == 1, min_time_list[1],
                If(friend1 == 2, min_time_list[2],
                   min_time_list[3])))
    
    available_start2 = If(friend2 == 0, available_start[0],
                      If(friend2 == 1, available_start[1],
                      If(friend2 == 2, available_start[2],
                         available_start[3])))
    available_end2 = If(friend2 == 0, available_end[0],
                    If(friend2 == 1, available_end[1],
                    If(friend2 == 2, available_end[2],
                       available_end[3])))
    min_time2 = If(friend2 == 0, min_time_list[0],
                If(friend2 == 1, min_time_list[1],
                If(friend2 == 2, min_time_list[2],
                   min_time_list[3])))
    
    available_start3 = If(friend3 == 0, available_start[0],
                      If(friend3 == 1, available_start[1],
                      If(friend3 == 2, available_start[2],
                         available_start[3])))
    available_end3 = If(friend3 == 0, available_end[0],
                    If(friend3 == 1, available_end[1],
                    If(friend3 == 2, available_end[2],
                       available_end[3])))
    min_time3 = If(friend3 == 0, min_time_list[0],
                If(friend3 == 1, min_time_list[1],
                If(friend3 == 2, min_time_list[2],
                   min_time_list[3])))
    
    arrival0 = 540 + travel_time0
    s.add(start0 >= arrival0)
    s.add(start0 >= available_start0)
    s.add(end0 == start0 + min_time0)
    s.add(end0 <= available_end0)
    
    arrival1 = end0 + travel_time1
    s.add(start1 >= arrival1)
    s.add(start1 >= available_start1)
    s.add(end1 == start1 + min_time1)
    s.add(end1 <= available_end1)
    
    arrival2 = end1 + travel_time2
    s.add(start2 >= arrival2)
    s.add(start2 >= available_start2)
    s.add(end2 == start2 + min_time2)
    s.add(end2 <= available_end2)
    
    arrival3 = end2 + travel_time3
    s.add(start3 >= arrival3)
    s.add(start3 >= available_start3)
    s.add(end3 == start3 + min_time3)
    s.add(end3 <= available_end3)
    
    if s.check() == sat:
        m = s.model()
        f0 = m[friend0].as_long()
        f1 = m[friend1].as_long()
        f2 = m[friend2].as_long()
        f3 = m[friend3].as_long()
        s0 = m[start0].as_long()
        e0 = m[end0].as_long()
        s1 = m[start1].as_long()
        e1 = m[end1].as_long()
        s2 = m[start2].as_long()
        e2 = m[end2].as_long()
        s3 = m[start3].as_long()
        e3 = m[end3].as_long()
        
        itinerary = [
            {"action": "meet", "person": friends_list[f0], "start_time": min_to_time(s0), "end_time": min_to_time(e0)},
            {"action": "meet", "person": friends_list[f1], "start_time": min_to_time(s1), "end_time": min_to_time(e1)},
            {"action": "meet", "person": friends_list[f2], "start_time": min_to_time(s2), "end_time": min_to_time(e2)},
            {"action": "meet", "person": friends_list[f3], "start_time": min_to_time(s3), "end_time": min_to_time(e3)}
        ]
        print('SOLUTION:')
        print(f'{{"itinerary": {itinerary}}}')
    else:
        print("No solution found for four meetings.")

if __name__ == '__main__':
    main()