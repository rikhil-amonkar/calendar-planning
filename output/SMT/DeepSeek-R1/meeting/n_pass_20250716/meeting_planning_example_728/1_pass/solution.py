from z3 import *

def minutes_to_time(minutes):
    total_minutes = int(minutes)
    hours = total_minutes // 60
    mins = total_minutes % 60
    total_hours = 9 + hours
    if total_hours < 12:
        period = "AM"
        display_hour = total_hours
    elif total_hours == 12:
        period = "PM"
        display_hour = 12
    else:
        display_hour = total_hours - 12
        period = "PM"
    if display_hour == 0:
        display_hour = 12
    return f"{display_hour}:{mins:02d}{period}"

def main():
    travel_dict = {
        "Marina District": {
            "Mission District": 20,
            "Fisherman's Wharf": 10,
            "Presidio": 10,
            "Union Square": 16,
            "Sunset District": 19,
            "Financial District": 17,
            "Haight-Ashbury": 16,
            "Russian Hill": 8
        },
        "Mission District": {
            "Marina District": 19,
            "Fisherman's Wharf": 22,
            "Presidio": 25,
            "Union Square": 15,
            "Sunset District": 24,
            "Financial District": 15,
            "Haight-Ashbury": 12,
            "Russian Hill": 15
        },
        "Fisherman's Wharf": {
            "Marina District": 9,
            "Mission District": 22,
            "Presidio": 17,
            "Union Square": 13,
            "Sunset District": 27,
            "Financial District": 11,
            "Haight-Ashbury": 22,
            "Russian Hill": 7
        },
        "Presidio": {
            "Marina District": 11,
            "Mission District": 26,
            "Fisherman's Wharf": 19,
            "Union Square": 22,
            "Sunset District": 15,
            "Financial District": 23,
            "Haight-Ashbury": 15,
            "Russian Hill": 14
        },
        "Union Square": {
            "Marina District": 18,
            "Mission District": 14,
            "Fisherman's Wharf": 15,
            "Presidio": 24,
            "Sunset District": 27,
            "Financial District": 9,
            "Haight-Ashbury": 18,
            "Russian Hill": 13
        },
        "Sunset District": {
            "Marina District": 21,
            "Mission District": 25,
            "Fisherman's Wharf": 29,
            "Presidio": 16,
            "Union Square": 30,
            "Financial District": 30,
            "Haight-Ashbury": 15,
            "Russian Hill": 24
        },
        "Financial District": {
            "Marina District": 15,
            "Mission District": 17,
            "Fisherman's Wharf": 10,
            "Presidio": 22,
            "Union Square": 9,
            "Sunset District": 30,
            "Haight-Ashbury": 19,
            "Russian Hill": 11
        },
        "Haight-Ashbury": {
            "Marina District": 17,
            "Mission District": 11,
            "Fisherman's Wharf": 23,
            "Presidio": 15,
            "Union Square": 19,
            "Sunset District": 15,
            "Financial District": 21,
            "Russian Hill": 17
        },
        "Russian Hill": {
            "Marina District": 7,
            "Mission District": 16,
            "Fisherman's Wharf": 7,
            "Presidio": 14,
            "Union Square": 10,
            "Sunset District": 23,
            "Financial District": 11,
            "Haight-Ashbury": 17
        }
    }
    
    friends = [
        ("Elizabeth", "Financial District", 75, 60, 225),
        ("Joseph", "Union Square", 120, 165, 345),
        ("Ashley", "Russian Hill", 45, 150, 750),
        ("Richard", "Fisherman's Wharf", 30, 330, 510),
        ("Kimberly", "Haight-Ashbury", 105, 315, 510),
        ("Karen", "Mission District", 30, 315, 780),
        ("Helen", "Sunset District", 105, 345, 705),
        ("Robert", "Presidio", 60, 765, 825)
    ]
    
    n = len(friends)
    
    s = Solver()
    
    meet = [Bool(f'meet_{i}') for i in range(n)]
    start = [Real(f'start_{i}') for i in range(n)]
    
    for i in range(n):
        name, district, min_dur, avail_start, avail_end = friends[i]
        s.add(Implies(meet[i], start[i] >= avail_start))
        s.add(Implies(meet[i], start[i] + min_dur <= avail_end))
        travel_time_from_marina = travel_dict["Marina District"][district]
        s.add(Implies(meet[i], start[i] >= travel_time_from_marina))
    
    for i in range(n):
        for j in range(i + 1, n):
            if i != j:
                name_i, district_i, min_dur_i, _, _ = friends[i]
                name_j, district_j, min_dur_j, _, _ = friends[j]
                travel_ij = travel_dict[district_i][district_j]
                travel_ji = travel_dict[district_j][district_i]
                constraint = Or(
                    start[j] >= start[i] + min_dur_i + travel_ij,
                    start[i] >= start[j] + min_dur_j + travel_ji
                )
                s.add(Implies(And(meet[i], meet[j]), constraint))
    
    num_meetings = Sum([If(meet[i], 1, 0) for i in range(n)])
    s.maximize(num_meetings)
    
    if s.check() == sat:
        m = s.model()
        total_met = 0
        schedule = []
        for i in range(n):
            if is_true(m.eval(meet[i])):
                total_met += 1
                start_val = m.eval(start[i])
                if isinstance(start_val, IntNumRef):
                    start_min = start_val.as_long()
                else:
                    start_min = int(str(start_val))
                end_min = start_min + friends[i][2]
                start_time_str = minutes_to_time(start_min)
                end_time_str = minutes_to_time(end_min)
                schedule.append((friends[i][0], friends[i][1], start_time_str, end_time_str))
        print(f"Total friends met: {total_met}")
        for name, district, start_time, end_time in schedule:
            print(f"Meet {name} at {district} from {start_time} to {end_time}")
    else:
        print("No valid schedule found.")

if __name__ == '__main__':
    main()