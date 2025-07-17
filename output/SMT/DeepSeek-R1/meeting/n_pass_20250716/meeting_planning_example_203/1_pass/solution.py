from z3 import *

def minutes_to_time(minutes):
    hours = 9 + minutes // 60
    minutes = minutes % 60
    am_pm = "AM" if hours < 12 else "PM"
    hours = hours if hours <= 12 else hours - 12
    return f"{hours}:{minutes:02d}{am_pm}"

def main():
    travel_times_dict = {
        ("FD", "FW"): 10,
        ("FD", "PH"): 13,
        ("FD", "MD"): 17,
        ("FW", "FD"): 11,
        ("FW", "PH"): 12,
        ("FW", "MD"): 22,
        ("PH", "FD"): 13,
        ("PH", "FW"): 13,
        ("PH", "MD"): 15,
        ("MD", "FD"): 17,
        ("MD", "FW"): 22,
        ("MD", "PH"): 16
    }
    
    s = Solver()
    first = Int('first')
    second = Int('second')
    third = Int('third')
    s.add(Distinct(first, second, third))
    s.add(first >= 0, first <= 2)
    s.add(second >= 0, second <= 2)
    s.add(third >= 0, third <= 2)
    
    T0 = Int('T0')
    T1 = Int('T1')
    T2 = Int('T2')
    T_d = Int('T_d')
    T_t = Int('T_t')
    T_r = Int('T_r')
    
    travel0 = Int('travel0')
    s.add(travel0 == If(first == 0, travel_times_dict[("FD", "FW")],
                   If(first == 1, travel_times_dict[("FD", "PH")],
                   travel_times_dict[("FD", "MD")])))
    
    travel1 = Int('travel1')
    cond1 = []
    for a in [0, 1, 2]:
        for b in [0, 1, 2]:
            if a == b:
                continue
            loc_a = "FW" if a == 0 else ("PH" if a == 1 else "MD")
            loc_b = "FW" if b == 0 else ("PH" if b == 1 else "MD")
            tt = travel_times_dict[(loc_a, loc_b)]
            cond1.append(And(first == a, second == b, travel1 == tt))
    s.add(Or(cond1))
    
    travel2 = Int('travel2')
    cond2 = []
    for a in [0, 1, 2]:
        for b in [0, 1, 2]:
            if a == b:
                continue
            loc_a = "FW" if a == 0 else ("PH" if a == 1 else "MD")
            loc_b = "FW" if b == 0 else ("PH" if b == 1 else "MD")
            tt = travel_times_dict[(loc_a, loc_b)]
            cond2.append(And(second == a, third == b, travel2 == tt))
    s.add(Or(cond2))
    
    dur0 = Int('dur0')
    s.add(dur0 == If(first == 0, 15, If(first == 1, 75, 90)))
    dur1 = Int('dur1')
    s.add(dur1 == If(second == 0, 15, If(second == 1, 75, 90)))
    dur2 = Int('dur2')
    s.add(dur2 == If(third == 0, 15, If(third == 1, 75, 90)))
    
    s.add(T0 == travel0)
    s.add(T1 == T0 + dur0 + travel1)
    s.add(T2 == T1 + dur1 + travel2)
    
    s.add(T_d == If(first == 0, T0, If(second == 0, T1, T2)))
    s.add(T_t == If(first == 1, T0, If(second == 1, T1, T2)))
    s.add(T_r == If(first == 2, T0, If(second == 2, T1, T2)))
    
    s.add(T_d >= 105, T_d <= 375)
    s.add(T_t >= 0, T_t <= 315)
    s.add(T_r >= 195, T_r <= 555)
    
    model = None
    if s.check() == sat:
        model = s.model()
        print("SOLUTION: Meet all three friends")
        T_d_val = model.eval(T_d).as_long()
        T_t_val = model.eval(T_t).as_long()
        T_r_val = model.eval(T_r).as_long()
        first_val = model.eval(first).as_long()
        second_val = model.eval(second).as_long()
        third_val = model.eval(third).as_long()
        locations = {0: 'Fisherman\'s Wharf', 1: 'Pacific Heights', 2: 'Mission District'}
        print(f"Order: 1st: {locations[first_val]}, 2nd: {locations[second_val]}, 3rd: {locations[third_val]}")
        print(f"Meet David at {minutes_to_time(T_d_val)}")
        print(f"Meet Timothy at {minutes_to_time(T_t_val)}")
        print(f"Meet Robert at {minutes_to_time(T_r_val)}")
        return
    
    two_friend_scenarios = [
        ([0, 1], "David and Timothy"),
        ([0, 2], "David and Robert"),
        ([1, 2], "Timothy and Robert")
    ]
    
    for friends, scenario_name in two_friend_scenarios:
        s2 = Solver()
        first = Int('first')
        second = Int('second')
        s2.add(Or([first == f for f in friends]))
        s2.add(Or([second == f for f in friends]))
        s2.add(first != second)
        s2.add(first >= 0, first <= 2)
        s2.add(second >= 0, second <= 2)
        
        T0 = Int('T0')
        T1 = Int('T1')
        T_d = Int('T_d')
        T_t = Int('T_t')
        T_r = Int('T_r')
        
        travel0 = Int('travel0')
        if friends == [0, 1]:
            s2.add(travel0 == If(first == 0, travel_times_dict[("FD", "FW")], travel_times_dict[("FD", "PH")]))
        elif friends == [0, 2]:
            s2.add(travel0 == If(first == 0, travel_times_dict[("FD", "FW")], travel_times_dict[("FD", "MD")]))
        elif friends == [1, 2]:
            s2.add(travel0 == If(first == 1, travel_times_dict[("FD", "PH")], travel_times_dict[("FD", "MD")]))
        
        travel1 = Int('travel1')
        if friends == [0, 1]:
            s2.add(travel1 == If(And(first == 0, second == 1), travel_times_dict[("FW", "PH")], travel_times_dict[("PH", "FW")]))
        elif friends == [0, 2]:
            s2.add(travel1 == If(And(first == 0, second == 2), travel_times_dict[("FW", "MD")], travel_times_dict[("MD", "FW")]))
        elif friends == [1, 2]:
            s2.add(travel1 == If(And(first == 1, second == 2), travel_times_dict[("PH", "MD")], travel_times_dict[("MD", "PH")]))
        
        dur0 = Int('dur0')
        s2.add(dur0 == If(first == 0, 15, If(first == 1, 75, 90)))
        dur1 = Int('dur1')
        s2.add(dur1 == If(second == 0, 15, If(second == 1, 75, 90)))
        
        s2.add(T0 == travel0)
        s2.add(T1 == T0 + dur0 + travel1)
        
        if 0 in friends:
            s2.add(T_d == If(first == 0, T0, T1))
        if 1 in friends:
            s2.add(T_t == If(first == 1, T0, T1))
        if 2 in friends:
            s2.add(T_r == If(first == 2, T0, T1))
        
        if 0 in friends:
            s2.add(T_d >= 105, T_d <= 375)
        if 1 in friends:
            s2.add(T_t >= 0, T_t <= 315)
        if 2 in friends:
            s2.add(T_r >= 195, T_r <= 555)
        
        if s2.check() == sat:
            model = s2.model()
            print(f"SOLUTION: Meet two friends: {scenario_name}")
            first_val = model.eval(first).as_long()
            second_val = model.eval(second).as_long()
            locations = {0: 'Fisherman\'s Wharf', 1: 'Pacific Heights', 2: 'Mission District'}
            print(f"Order: 1st: {locations[first_val]}, 2nd: {locations[second_val]}")
            if 0 in friends:
                T_d_val = model.eval(T_d).as_long()
                print(f"Meet David at {minutes_to_time(T_d_val)}")
            if 1 in friends:
                T_t_val = model.eval(T_t).as_long()
                print(f"Meet Timothy at {minutes_to_time(T_t_val)}")
            if 2 in friends:
                T_r_val = model.eval(T_r).as_long()
                print(f"Meet Robert at {minutes_to_time(T_r_val)}")
            return
    
    one_friend_scenarios = [
        (0, "David"),
        (1, "Timothy"),
        (2, "Robert")
    ]
    
    for friend, name in one_friend_scenarios:
        s3 = Solver()
        travel = Int('travel')
        T_friend = Int('T_friend')
        if friend == 0:
            s3.add(travel == travel_times_dict[("FD", "FW")])
            s3.add(T_friend == travel)
            s3.add(T_friend >= 105, T_friend <= 375)
        elif friend == 1:
            s3.add(travel == travel_times_dict[("FD", "PH")])
            s3.add(T_friend == travel)
            s3.add(T_friend >= 0, T_friend <= 315)
        elif friend == 2:
            s3.add(travel == travel_times_dict[("FD", "MD")])
            s3.add(T_friend == travel)
            s3.add(T_friend >= 195, T_friend <= 555)
        
        if s3.check() == sat:
            model = s3.model()
            T_val = model.eval(T_friend).as_long()
            print(f"SOLUTION: Meet one friend: {name}")
            print(f"Meet {name} at {minutes_to_time(T_val)}")
            return

if __name__ == "__main__":
    main()