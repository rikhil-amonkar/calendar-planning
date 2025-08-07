from z3 import *
import json

def main():
    friends = [
        ('Elizabeth', 'Marina District', 1140, 1245, 105),   # 7:00 PM to 8:45 PM
        ('Joshua', 'Presidio', 510, 795, 105),                # 8:30 AM to 1:15 PM
        ('Timothy', 'North Beach', 1185, 1320, 90),           # 7:45 PM to 10:00 PM
        ('David', 'Embarcadero', 645, 750, 30),               # 10:45 AM to 12:30 PM
        ('Kimberly', 'Haight-Ashbury', 1005, 1290, 75),       # 4:45 PM to 9:30 PM
        ('Lisa', 'Golden Gate Park', 1050, 1305, 45),         # 5:30 PM to 9:45 PM
        ('Stephanie', 'Alamo Square', 930, 990, 30),          # 3:30 PM to 4:30 PM
        ('Helen', 'Financial District', 1050, 1110, 45),      # 5:30 PM to 6:30 PM
        ('Laura', 'Sunset District', 1065, 1290, 90)          # 5:45 PM to 9:15 PM
    ]

    travel_dict = {
        "The Castro": {
            "Marina District": 21,
            "Presidio": 20,
            "North Beach": 20,
            "Embarcadero": 22,
            "Haight-Ashbury": 6,
            "Golden Gate Park": 11,
            "Alamo Square": 8,
            "Financial District": 21,
            "Sunset District": 17
        },
        "Marina District": {
            "The Castro": 22,
            "Presidio": 10,
            "North Beach": 11,
            "Embarcadero": 14,
            "Haight-Ashbury": 16,
            "Golden Gate Park": 18,
            "Alamo Square": 15,
            "Financial District": 17,
            "Sunset District": 19
        },
        "Presidio": {
            "The Castro": 21,
            "Marina District": 11,
            "North Beach": 18,
            "Embarcadero": 20,
            "Haight-Ashbury": 15,
            "Golden Gate Park": 12,
            "Alamo Square": 19,
            "Financial District": 23,
            "Sunset District": 15
        },
        "North Beach": {
            "The Castro": 23,
            "Marina District": 9,
            "Presidio": 17,
            "Embarcadero": 6,
            "Haight-Ashbury": 18,
            "Golden Gate Park": 22,
            "Alamo Square": 16,
            "Financial District": 8,
            "Sunset District": 27
        },
        "Embarcadero": {
            "The Castro": 25,
            "Marina District": 12,
            "Presidio": 20,
            "North Beach": 5,
            "Haight-Ashbury": 21,
            "Golden Gate Park": 25,
            "Alamo Square": 19,
            "Financial District": 5,
            "Sunset District": 30
        },
        "Haight-Ashbury": {
            "The Castro": 6,
            "Marina District": 17,
            "Presidio": 15,
            "North Beach": 19,
            "Embarcadero": 20,
            "Golden Gate Park": 7,
            "Alamo Square": 5,
            "Financial District": 21,
            "Sunset District": 15
        },
        "Golden Gate Park": {
            "The Castro": 13,
            "Marina District": 16,
            "Presidio": 11,
            "North Beach": 23,
            "Embarcadero": 25,
            "Haight-Ashbury": 7,
            "Alamo Square": 9,
            "Financial District": 26,
            "Sunset District": 10
        },
        "Alamo Square": {
            "The Castro": 8,
            "Marina District": 15,
            "Presidio": 17,
            "North Beach": 15,
            "Embarcadero": 16,
            "Haight-Ashbury": 5,
            "Golden Gate Park": 9,
            "Financial District": 17,
            "Sunset District": 16
        },
        "Financial District": {
            "The Castro": 20,
            "Marina District": 15,
            "Presidio": 22,
            "North Beach": 7,
            "Embarcadero": 4,
            "Haight-Ashbury": 19,
            "Golden Gate Park": 23,
            "Alamo Square": 17,
            "Sunset District": 30
        },
        "Sunset District": {
            "The Castro": 17,
            "Marina District": 21,
            "Presidio": 16,
            "North Beach": 28,
            "Embarcadero": 30,
            "Haight-Ashbury": 15,
            "Golden Gate Park": 11,
            "Alamo Square": 17,
            "Financial District": 30
        }
    }

    s = Optimize()
    meet_vars = {}
    start_vars = {}
    end_vars = {}

    for name, loc, avail_start, avail_end, dur_min in friends:
        meet_vars[name] = Bool(name)
        start_vars[name] = Int(f"start_{name}")
        end_vars[name] = start_vars[name] + dur_min

        # If we meet this friend, then the meeting must be within their window
        s.add(Implies(meet_vars[name], start_vars[name] >= avail_start))
        s.add(Implies(meet_vars[name], end_vars[name] <= avail_end))
        # Also, we must be able to get from The Castro to the friend's location, considering travel time
        s.add(Implies(meet_vars[name], start_vars[name] >= 540 + travel_dict["The Castro"][loc]))

    friend_names = [name for name, _, _, _, _ in friends]
    n = len(friend_names)
    for i in range(n):
        for j in range(i+1, n):
            name_i = friend_names[i]
            name_j = friend_names[j]
            loc_i = friends[i][1]
            loc_j = friends[j][1]
            # Constraint for the pair: either i comes before j or j comes before i, with travel time
            constraint = Or(
                end_vars[name_i] + travel_dict[loc_i][loc_j] <= start_vars[name_j],
                end_vars[name_j] + travel_dict[loc_j][loc_i] <= start_vars[name_i]
            )
            s.add(Implies(And(meet_vars[name_i], meet_vars[name_j]), constraint))

    # Maximize the number of friends met
    s.maximize(Sum([If(meet_vars[name], 1, 0) for name in friend_names]))
    
    if s.check() == sat:
        m = s.model()
        scheduled_meetings = []
        for name, _, _, _, dur_min in friends:
            if is_true(m[meet_vars[name]]):
                start_val = m[start_vars[name]].as_long()
                end_val = start_val + dur_min
                start_hour = start_val // 60
                start_minute = start_val % 60
                end_hour = end_val // 60
                end_minute = end_val % 60
                scheduled_meetings.append({
                    "action": "meet",
                    "person": name,
                    "start_time": f"{start_hour:02d}:{start_minute:02d}",
                    "end_time": f"{end_hour:02d}:{end_minute:02d}"
                })
        scheduled_meetings.sort(key=lambda x: (int(x['start_time'][:2]), int(x['start_time'][3:5])))
        result = {"itinerary": scheduled_meetings}
        print("SOLUTION:")
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()