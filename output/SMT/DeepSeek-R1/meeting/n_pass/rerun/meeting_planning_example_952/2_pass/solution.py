from z3 import *

def main():
    # List of friends: (name, location, window_start (minutes from 9:00AM), window_end, min_duration)
    friends = [
        ("Brian", "North Beach", 240, 600, 90),
        ("Richard", "Fisherman's Wharf", 120, 225, 60),
        ("Ashley", "Haight-Ashbury", 360, 690, 90),
        ("Elizabeth", "Nob Hill", 165, 570, 75),
        ("Jessica", "Golden Gate Park", 660, 765, 105),
        ("Deborah", "Union Square", 510, 780, 60),
        ("Kimberly", "Alamo Square", 510, 735, 45),
        ("Matthew", "Presidio", -45, 0, 15),
        ("Kenneth", "Chinatown", 285, 630, 105),
        ("Anthony", "Pacific Heights", 315, 420, 30)
    ]
    
    # Build travel time dictionary
    travel_dict = {
        "Bayview": {
            "North Beach": 22,
            "Fisherman's Wharf": 25,
            "Haight-Ashbury": 19,
            "Nob Hill": 20,
            "Golden Gate Park": 22,
            "Union Square": 18,
            "Alamo Square": 16,
            "Presidio": 32,
            "Chinatown": 19,
            "Pacific Heights": 23
        },
        "North Beach": {
            "Bayview": 25,
            "Fisherman's Wharf": 5,
            "Haight-Ashbury": 18,
            "Nob Hill": 7,
            "Golden Gate Park": 22,
            "Union Square": 7,
            "Alamo Square": 16,
            "Presidio": 17,
            "Chinatown": 6,
            "Pacific Heights": 8
        },
        "Fisherman's Wharf": {
            "Bayview": 26,
            "North Beach": 6,
            "Haight-Ashbury": 22,
            "Nob Hill": 11,
            "Golden Gate Park": 25,
            "Union Square": 13,
            "Alamo Square": 21,
            "Presidio": 17,
            "Chinatown": 12,
            "Pacific Heights": 12
        },
        "Haight-Ashbury": {
            "Bayview": 18,
            "North Beach": 19,
            "Fisherman's Wharf": 23,
            "Nob Hill": 15,
            "Golden Gate Park": 7,
            "Union Square": 19,
            "Alamo Square": 5,
            "Presidio": 15,
            "Chinatown": 19,
            "Pacific Heights": 12
        },
        "Nob Hill": {
            "Bayview": 19,
            "North Beach": 8,
            "Fisherman's Wharf": 10,
            "Haight-Ashbury": 13,
            "Golden Gate Park": 17,
            "Union Square": 7,
            "Alamo Square": 11,
            "Presidio": 17,
            "Chinatown": 6,
            "Pacific Heights": 8
        },
        "Golden Gate Park": {
            "Bayview": 23,
            "North Beach": 23,
            "Fisherman's Wharf": 24,
            "Haight-Ashbury": 7,
            "Nob Hill": 20,
            "Union Square": 22,
            "Alamo Square": 9,
            "Presidio": 11,
            "Chinatown": 23,
            "Pacific Heights": 16
        },
        "Union Square": {
            "Bayview": 15,
            "North Beach": 10,
            "Fisherman's Wharf": 15,
            "Haight-Ashbury": 18,
            "Nob Hill": 9,
            "Golden Gate Park": 22,
            "Alamo Square": 15,
            "Presidio": 24,
            "Chinatown": 7,
            "Pacific Heights": 15
        },
        "Alamo Square": {
            "Bayview": 16,
            "North Beach": 15,
            "Fisherman's Wharf": 19,
            "Haight-Ashbury": 5,
            "Nob Hill": 11,
            "Golden Gate Park": 9,
            "Union Square": 14,
            "Presidio": 17,
            "Chinatown": 15,
            "Pacific Heights": 10
        },
        "Presidio": {
            "Bayview": 31,
            "North Beach": 18,
            "Fisherman's Wharf": 19,
            "Haight-Ashbury": 15,
            "Nob Hill": 18,
            "Golden Gate Park": 12,
            "Union Square": 22,
            "Alamo Square": 19,
            "Chinatown": 21,
            "Pacific Heights": 11
        },
        "Chinatown": {
            "Bayview": 20,
            "North Beach": 3,
            "Fisherman's Wharf": 8,
            "Haight-Ashbury": 19,
            "Nob Hill": 9,
            "Golden Gate Park": 23,
            "Union Square": 7,
            "Alamo Square": 17,
            "Presidio": 19,
            "Pacific Heights": 10
        },
        "Pacific Heights": {
            "Bayview": 22,
            "North Beach": 9,
            "Fisherman's Wharf": 13,
            "Haight-Ashbury": 11,
            "Nob Hill": 8,
            "Golden Gate Park": 15,
            "Union Square": 12,
            "Alamo Square": 10,
            "Presidio": 11,
            "Chinatown": 11
        }
    }
    
    opt = Optimize()
    
    meet_dict = {}
    start_dict = {}
    end_dict = {}
    
    # Meeting index -1 is the start at Bayview
    meet_dict[-1] = True
    start_dict[-1] = 0
    end_dict[-1] = 0
    
    # Create variables for friends 0 to 9
    for i in range(10):
        meet_dict[i] = Bool(f"meet_{i}")
        start_dict[i] = Int(f"start_{i}")
        end_dict[i] = Int(f"end_{i}")
    
    # Helper function to get travel time between two meetings
    def get_travel_time(i, j):
        if i == -1:
            loc_i = "Bayview"
        else:
            loc_i = friends[i][1]
        if j == -1:
            loc_j = "Bayview"
        else:
            loc_j = friends[j][1]
        return travel_dict[loc_i][loc_j]
    
    # Constraints for each friend
    for i in range(10):
        name, loc, win_start, win_end, dur = friends[i]
        opt.add(Implies(meet_dict[i], start_dict[i] >= win_start))
        opt.add(Implies(meet_dict[i], end_dict[i] <= win_end))
        opt.add(Implies(meet_dict[i], end_dict[i] == start_dict[i] + dur))
    
    # Pairwise constraints for all distinct pairs of meetings (including Bayview)
    meeting_indices = [-1] + list(range(10))
    for i in meeting_indices:
        for j in meeting_indices:
            if i == j:
                continue
            meet_i = meet_dict[i] if i != -1 else True
            meet_j = meet_dict[j] if j != -1 else True
            travel_ij = get_travel_time(i, j)
            travel_ji = get_travel_time(j, i)
            opt.add(Implies(And(meet_i, meet_j),
                         Or(start_dict[j] >= end_dict[i] + travel_ij, 
                            start_dict[i] >= end_dict[j] + travel_ji)))
    
    # Objective: maximize the number of friends met
    objective = Sum([If(meet_dict[i], 1, 0) for i in range(10)])
    opt.maximize(objective)
    
    if opt.check() == sat:
        m = opt.model()
        total_met = sum(1 for i in range(10) if is_true(m.eval(meet_dict[i])))
        print(f"SOLUTION: Met {total_met} friends.")
        schedule = []
        for i in range(10):
            if is_true(m.eval(meet_dict[i])):
                start_val = m.eval(start_dict[i])
                if isinstance(start_val, IntNumRef):
                    start_val = start_val.as_long()
                else:
                    start_val = int(str(start_val))
                name = friends[i][0]
                loc = friends[i][1]
                end_val = start_val + friends[i][4]
                total_minutes = start_val
                hours = total_minutes // 60
                minutes = total_minutes % 60
                hour_of_day = 9 + hours
                am_pm = "AM"
                if hour_of_day >= 12:
                    am_pm = "PM"
                    if hour_of_day > 12:
                        hour_of_day -= 12
                start_str = f"{hour_of_day}:{minutes:02d}{am_pm}"
                schedule.append((start_val, name, loc, start_str))
        schedule.sort(key=lambda x: x[0])
        for item in schedule:
            print(f"Meet {item[1]} at {item[2]} starting at {item[3]}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()