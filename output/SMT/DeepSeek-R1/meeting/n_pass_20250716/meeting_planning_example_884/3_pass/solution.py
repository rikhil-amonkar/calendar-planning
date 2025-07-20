from z3 import *

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    am_pm = "AM" if hours < 12 else "PM"
    if hours > 12:
        hours -= 12
    elif hours == 0:
        hours = 12
    return f"{hours}:{mins:02d}{am_pm}"

def main():
    base = 9 * 60  # 9:00 AM in minutes from midnight

    # Travel times dictionary
    travel_dict = {
        "Richmond District": {
            "Chinatown": 20,
            "Sunset District": 11,
            "Alamo Square": 13,
            "Financial District": 22,
            "North Beach": 17,
            "Embarcadero": 19,
            "Presidio": 7,
            "Golden Gate Park": 9,
            "Bayview": 27
        },
        "Chinatown": {
            "Richmond District": 20,
            "Sunset District": 29,
            "Alamo Square": 17,
            "Financial District": 5,
            "North Beach": 3,
            "Embarcadero": 5,
            "Presidio": 19,
            "Golden Gate Park": 23,
            "Bayview": 20
        },
        "Sunset District": {
            "Richmond District": 12,
            "Chinatown": 30,
            "Alamo Square": 17,
            "Financial District": 30,
            "North Beach": 28,
            "Embarcadero": 30,
            "Presidio": 16,
            "Golden Gate Park": 11,
            "Bayview": 22
        },
        "Alamo Square": {
            "Richmond District": 11,
            "Chinatown": 15,
            "Sunset District": 16,
            "Financial District": 17,
            "North Beach": 15,
            "Embarcadero": 16,
            "Presidio": 17,
            "Golden Gate Park": 9,
            "Bayview": 16
        },
        "Financial District": {
            "Richmond District": 21,
            "Chinatown": 5,
            "Sunset District": 30,
            "Alamo Square": 17,
            "North Beach": 7,
            "Embarcadero": 4,
            "Presidio": 22,
            "Golden Gate Park": 23,
            "Bayview": 19
        },
        "North Beach": {
            "Richmond District": 18,
            "Chinatown": 6,
            "Sunset District": 27,
            "Alamo Square": 16,
            "Financial District": 8,
            "Embarcadero": 6,
            "Presidio": 17,
            "Golden Gate Park": 22,
            "Bayview": 25
        },
        "Embarcadero": {
            "Richmond District": 21,
            "Chinatown": 7,
            "Sunset District": 30,
            "Alamo Square": 19,
            "Financial District": 5,
            "North Beach": 5,
            "Presidio": 20,
            "Golden Gate Park": 25,
            "Bayview": 21
        },
        "Presidio": {
            "Richmond District": 7,
            "Chinatown": 21,
            "Sunset District": 15,
            "Alamo Square": 19,
            "Financial District": 23,
            "North Beach": 18,
            "Embarcadero": 20,
            "Golden Gate Park": 12,
            "Bayview": 31
        },
        "Golden Gate Park": {
            "Richmond District": 7,
            "Chinatown": 23,
            "Sunset District": 10,
            "Alamo Square": 9,
            "Financial District": 26,
            "North Beach": 23,
            "Embarcadero": 25,
            "Presidio": 11,
            "Bayview": 23
        },
        "Bayview": {
            "Richmond District": 25,
            "Chinatown": 19,
            "Sunset District": 23,
            "Alamo Square": 16,
            "Financial District": 19,
            "North Beach": 22,
            "Embarcadero": 19,
            "Presidio": 32,
            "Golden Gate Park": 22
        }
    }

    # Add self-loops with 0 travel time to avoid KeyError
    for loc in list(travel_dict.keys()):
        travel_dict[loc][loc] = 0

    friends = [
        ("Robert", "Chinatown", (7*60+45, 17*60+30), 120),
        ("David", "Sunset District", (12*60+30, 19*60+45), 45),
        ("Matthew", "Alamo Square", (8*60+45, 13*60+45), 90),
        ("Jessica", "Financial District", (9*60+30, 18*60+45), 45),
        ("Melissa", "North Beach", (7*60+15, 16*60+45), 45),
        ("Mark", "Embarcadero", (15*60+15, 17*60+0), 45),
        ("Deborah", "Presidio", (19*60+0, 19*60+45), 45),
        ("Karen", "Golden Gate Park", (19*60+30, 22*60+0), 120),
        ("Laura", "Bayview", (21*60+15, 22*60+15), 15)
    ]

    n = len(friends)

    seq = [Int(f'seq_{i}') for i in range(n)]
    meet = [Bool(f'meet_{i}') for i in range(n)]
    start = [Int(f'start_{i}') for i in range(n)]  # Changed to Int
    dur = [Int(f'dur_{i}') for i in range(n)]      # Changed to Int

    opt = Optimize()

    for i in range(n):
        opt.add(Or(seq[i] == -1, And(seq[i] >= 0, seq[i] < n)))
    
    for i in range(n-1):
        opt.add(Implies(seq[i] == -1, seq[i+1] == -1))
    
    for i in range(n):
        opt.add(meet[i] == Or([seq[k] == i for k in range(n)]))
    
    for i in range(n):
        for j in range(i+1, n):
            opt.add(Implies(And(seq[i] != -1, seq[j] != -1), seq[i] != seq[j]))
    
    for i in range(n):
        name, loc, (avail_start, avail_end), min_dur_val = friends[i]
        opt.add(Implies(meet[i], And(
            start[i] >= avail_start,
            dur[i] >= min_dur_val,
            start[i] + dur[i] <= avail_end
        )))
    
    for k in range(n):
        if k == 0:
            for i in range(n):
                loc_i = friends[i][1]
                travel_time_i = travel_dict["Richmond District"][loc_i]
                opt.add(Implies(And(seq[0] != -1, seq[0] == i), start[i] >= base + travel_time_i))
        else:
            for i in range(n):
                for j in range(n):
                    loc_j = friends[j][1]
                    loc_i = friends[i][1]
                    travel_time_ji = travel_dict[loc_j][loc_i]
                    opt.add(Implies(And(seq[k] != -1, seq[k] == i, seq[k-1] == j),
                        start[i] >= start[j] + dur[j] + travel_time_ji))
    
    obj = Sum([If(meet[i], 1, 0) for i in range(n)])
    opt.maximize(obj)
    
    if opt.check() == sat:
        m = opt.model()
        total_meetings = m.evaluate(obj).as_long()
        print(f"Total meetings: {total_meetings}")
        
        seq_vals = [m.evaluate(seq[i]).as_long() for i in range(n)]
        start_vals = [m.evaluate(start[i]).as_long() for i in range(n)]
        dur_vals = [m.evaluate(dur[i]).as_long() for i in range(n)]
        
        start_times = start_vals
        dur_times = dur_vals
        end_times = [start_times[i] + dur_times[i] for i in range(n)]
        
        print("\nSchedule:")
        current_location = "Richmond District"
        current_time = base
        for k in range(n):
            if seq_vals[k] == -1:
                break
            friend_idx = seq_vals[k]
            name, loc, _, _ = friends[friend_idx]
            travel_time = travel_dict[current_location][loc]
            travel_start = current_time
            travel_end = current_time + travel_time
            meeting_start = start_times[friend_idx]
            meeting_end = end_times[friend_idx]
            meeting_duration = dur_times[friend_idx]
            
            print(f"Travel from {current_location} to {loc}: {minutes_to_time(travel_start)} to {minutes_to_time(travel_end)} (Duration: {travel_time} minutes)")
            print(f"Meet {name} at {loc}: {minutes_to_time(meeting_start)} to {minutes_to_time(meeting_end)} (Duration: {meeting_duration} minutes)")
            
            current_location = loc
            current_time = meeting_end
            
        print("\nMeeting Details:")
        for i in range(n):
            name, loc, (avail_start, avail_end), min_dur_val = friends[i]
            if m.evaluate(meet[i]):
                s_time = start_times[i]
                d_time = dur_times[i]
                e_time = end_times[i]
                print(f"{name} at {loc}: {minutes_to_time(s_time)} to {minutes_to_time(e_time)} (Duration: {d_time} minutes) [Within window: {minutes_to_time(avail_start)} to {minutes_to_time(avail_end)}, Min Duration: {min_dur_val}]")
            else:
                print(f"{name} at {loc}: Not met")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()