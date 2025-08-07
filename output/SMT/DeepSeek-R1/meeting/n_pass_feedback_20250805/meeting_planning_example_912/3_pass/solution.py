import json
from z3 import *

def main():
    # Convert time string to minutes from 9:00 AM
    def time_to_minutes(t_str):
        parts = t_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1])
        total_minutes = hour * 60 + minute
        return total_minutes - 540  # 9:00 AM is 540 minutes from 00:00

    # Meetings data: (name, location, start_avail_min, end_avail_min, min_duration_min)
    meetings_data = [
        ("Kimberly", "Presidio", time_to_minutes("15:30"), time_to_minutes("16:00"), 15),
        ("Elizabeth", "Alamo Square", time_to_minutes("19:15"), time_to_minutes("20:15"), 15),
        ("Joshua", "Marina District", time_to_minutes("10:30"), time_to_minutes("14:15"), 45),
        ("Sandra", "Financial District", time_to_minutes("19:30"), time_to_minutes("20:15"), 45),
        ("Kenneth", "Nob Hill", time_to_minutes("12:45"), time_to_minutes("21:45"), 30),
        ("Betty", "Sunset District", time_to_minutes("14:00"), time_to_minutes("19:00"), 60),
        ("Deborah", "Chinatown", time_to_minutes("17:15"), time_to_minutes("20:30"), 15),
        ("Barbara", "Russian Hill", time_to_minutes("17:30"), time_to_minutes("21:15"), 120),
        ("Steven", "North Beach", time_to_minutes("17:45"), time_to_minutes("20:45"), 90),
        ("Daniel", "Haight-Ashbury", time_to_minutes("18:30"), time_to_minutes("18:45"), 15)
    ]

    # Build travel time dictionary
    locations = ["Presidio", "Alamo Square", "Marina District", "Financial District", "Nob Hill", 
                 "Sunset District", "Chinatown", "Russian Hill", "North Beach", "Haight-Ashbury"]
    travel_dict = {}
    travel_dict["Union Square"] = {
        "Presidio": 24,
        "Alamo Square": 15,
        "Marina District": 18,
        "Financial District": 9,
        "Nob Hill": 9,
        "Sunset District": 27,
        "Chinatown": 7,
        "Russian Hill": 13,
        "North Beach": 10,
        "Haight-Ashbury": 18
    }
    travel_dict["Presidio"] = {
        "Union Square": 22,
        "Alamo Square": 19,
        "Marina District": 11,
        "Financial District": 23,
        "Nob Hill": 18,
        "Sunset District": 15,
        "Chinatown": 21,
        "Russian Hill": 14,
        "North Beach": 18,
        "Haight-Ashbury": 15
    }
    travel_dict["Alamo Square"] = {
        "Union Square": 14,
        "Presidio": 17,
        "Marina District": 15,
        "Financial District": 17,
        "Nob Hill": 11,
        "Sunset District": 16,
        "Chinatown": 15,
        "Russian Hill": 13,
        "North Beach": 15,
        "Haight-Ashbury": 5
    }
    travel_dict["Marina District"] = {
        "Union Square": 16,
        "Presidio": 10,
        "Alamo Square": 15,
        "Financial District": 17,
        "Nob Hill": 12,
        "Sunset District": 19,
        "Chinatown": 15,
        "Russian Hill": 8,
        "North Beach": 11,
        "Haight-Ashbury": 16
    }
    travel_dict["Financial District"] = {
        "Union Square": 9,
        "Presidio": 22,
        "Alamo Square": 17,
        "Marina District": 15,
        "Nob Hill": 8,
        "Sunset District": 30,
        "Chinatown": 5,
        "Russian Hill": 11,
        "North Beach": 7,
        "Haight-Ashbury": 19
    }
    travel_dict["Nob Hill"] = {
        "Union Square": 7,
        "Presidio": 17,
        "Alamo Square": 11,
        "Marina District": 11,
        "Financial District": 9,
        "Sunset District": 24,
        "Chinatown": 6,
        "Russian Hill": 5,
        "North Beach": 8,
        "Haight-Ashbury": 13
    }
    travel_dict["Sunset District"] = {
        "Union Square": 30,
        "Presidio": 16,
        "Alamo Square": 17,
        "Marina District": 21,
        "Financial District": 30,
        "Nob Hill": 27,
        "Chinatown": 30,
        "Russian Hill": 24,
        "North Beach": 28,
        "Haight-Ashbury": 15
    }
    travel_dict["Chinatown"] = {
        "Union Square": 7,
        "Presidio": 19,
        "Alamo Square": 17,
        "Marina District": 12,
        "Financial District": 5,
        "Nob Hill": 9,
        "Sunset District": 29,
        "Russian Hill": 7,
        "North Beach": 3,
        "Haight-Ashbury": 19
    }
    travel_dict["Russian Hill"] = {
        "Union Square": 10,
        "Presidio": 14,
        "Alamo Square": 15,
        "Marina District": 7,
        "Financial District": 11,
        "Nob Hill": 5,
        "Sunset District": 23,
        "Chinatown": 9,
        "North Beach": 5,
        "Haight-Ashbury": 17
    }
    travel_dict["North Beach"] = {
        "Union Square": 7,
        "Presidio": 17,
        "Alamo Square": 16,
        "Marina District": 9,
        "Financial District": 8,
        "Nob Hill": 7,
        "Sunset District": 27,
        "Chinatown": 6,
        "Russian Hill": 4,
        "Haight-Ashbury": 18
    }
    travel_dict["Haight-Ashbury"] = {
        "Union Square": 19,
        "Presidio": 15,
        "Alamo Square": 5,
        "Marina District": 17,
        "Financial District": 21,
        "Nob Hill": 15,
        "Sunset District": 15,
        "Chinatown": 19,
        "Russian Hill": 17,
        "North Beach": 19
    }

    n = len(meetings_data)
    s = Solver()

    # Activity flags
    active = [Bool(f'active_{i}') for i in range(n)]
    # Position in the sequence for active meetings, -1 for inactive
    position = [Int(f'position_{i}') for i in range(n)]
    # Start and end times (in minutes from 9:00 AM)
    start_time = [Real(f'start_{i}') for i in range(n)]
    end_time = [Real(f'end_{i}') for i in range(n)]

    # Travel times from Union Square to each meeting location
    travel_from_union = [travel_dict['Union Square'][meetings_data[i][1]] for i in range(n)]
    # Travel times between meetings: travel_matrix[i][j] = travel time from location_i to location_j
    travel_matrix = []
    for i in range(n):
        loc_i = meetings_data[i][1]
        row = []
        for j in range(n):
            loc_j = meetings_data[j][1]
            if loc_i == loc_j:
                row.append(0)
            else:
                row.append(travel_dict[loc_i][loc_j])
        travel_matrix.append(row)

    # k = number of active meetings
    k = Int('k')
    s.add(k == Sum([If(active[i], 1, 0) for i in range(n)]))

    # Constraints for each meeting
    for i in range(n):
        name, loc, avail_start, avail_end, min_dur = meetings_data[i]
        # If active, set up times and position
        s.add(Implies(active[i], 
                      And(start_time[i] >= avail_start, 
                          end_time[i] == start_time[i] + min_dur,
                          end_time[i] <= avail_end,
                          position[i] >= 0,
                          position[i] < k)))
        # If inactive, set position to -1 and times to 0 (arbitrary)
        s.add(Implies(Not(active[i]), 
                      And(position[i] == -1,
                          start_time[i] == 0,
                          end_time[i] == 0)))

    # Distinct positions for active meetings
    for i in range(n):
        for j in range(i+1, n):
            s.add(Implies(And(active[i], active[j]), position[i] != position[j]))

    # Contiguous positions: for each active meeting with position>0, there is an active meeting with position-1
    for i in range(n):
        or_terms = []
        for j in range(n):
            if i == j:
                continue
            or_terms.append(And(active[j], position[j] == position[i] - 1))
        s.add(Implies(And(active[i], position[i] > 0), Or(or_terms)))

    # Travel constraints:
    # For the first meeting (position=0), must start after travel from Union Square
    for i in range(n):
        s.add(Implies(And(active[i], position[i] == 0), 
                      start_time[i] >= travel_from_union[i]))
    
    # For consecutive meetings: if j comes right after i, then start_time[j] >= end_time[i] + travel_time(i,j)
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            s.add(Implies(And(active[i], active[j], position[j] == position[i] + 1),
                           start_time[j] >= end_time[i] + travel_matrix[i][j]))

    # Use Optimize solver to maximize k
    opt = Optimize()
    opt.add(s.assertions())
    opt.maximize(k)  # Correctly maximize k using the Optimize solver

    if opt.check() == sat:
        m = opt.model()
        active_meetings = []
        for i in range(n):
            if is_true(m.evaluate(active[i])):
                name = meetings_data[i][0]
                start_val = m.evaluate(start_time[i])
                end_val = m.evaluate(end_time[i])
                # Convert to integer minutes and then to HH:MM
                start_minutes = int(str(start_val).split('/')[0]) if '/' in str(start_val) else int(float(str(start_val)))
                end_minutes = int(str(end_val).split('/')[0]) if '/' in str(end_val) else int(float(str(end_val)))
                # Convert minutes from 9:00 to absolute time
                start_abs = 540 + start_minutes
                end_abs = 540 + end_minutes
                start_h = start_abs // 60
                start_m = start_abs % 60
                end_h = end_abs // 60
                end_m = end_abs % 60
                start_str = f"{start_h:02d}:{start_m:02d}"
                end_str = f"{end_h:02d}:{end_m:02d}"
                active_meetings.append({
                    "action": "meet",
                    "person": name,
                    "start_time": start_str,
                    "end_time": end_str
                })
        # Sort meetings by start_time
        active_meetings.sort(key=lambda x: (int(x['start_time'].split(':')[0]), int(x['start_time'].split(':')[1])))
        result = {"itinerary": active_meetings}
        print("SOLUTION:")
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()