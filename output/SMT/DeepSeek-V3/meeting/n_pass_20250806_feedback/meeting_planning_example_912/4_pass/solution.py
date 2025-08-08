from z3 import *
import json

def solve_scheduling():
    s = Optimize()

    # Define friends and their constraints
    friends = {
        "Kimberly": {"location": "Presidio", "available_start": "15:30", "available_end": "16:00", "min_duration": 15},
        "Elizabeth": {"location": "Alamo Square", "available_start": "19:15", "available_end": "20:15", "min_duration": 15},
        "Joshua": {"location": "Marina District", "available_start": "10:30", "available_end": "14:15", "min_duration": 45},
        "Sandra": {"location": "Financial District", "available_start": "19:30", "available_end": "20:15", "min_duration": 45},
        "Kenneth": {"location": "Nob Hill", "available_start": "12:45", "available_end": "21:45", "min_duration": 30},
        "Betty": {"location": "Sunset District", "available_start": "14:00", "available_end": "19:00", "min_duration": 60},
        "Deborah": {"location": "Chinatown", "available_start": "17:15", "available_end": "20:30", "min_duration": 15},
        "Barbara": {"location": "Russian Hill", "available_start": "17:30", "available_end": "21:15", "min_duration": 120},
        "Steven": {"location": "North Beach", "available_start": "17:45", "available_end": "20:45", "min_duration": 90},
        "Daniel": {"location": "Haight-Ashbury", "available_start": "18:30", "available_end": "18:45", "min_duration": 15}
    }

    # Time conversion functions
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm - 540  # 9:00 AM is 540 minutes

    def minutes_to_time(minutes):
        total_minutes = 540 + minutes
        hh = total_minutes // 60
        mm = total_minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Travel times (simplified symmetric version)
    travel_times = {
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Alamo Square"): 15,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Sunset District"): 27,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Russian Hill"): 13,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Chinatown"): 15,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Financial District", "Nob Hill"): 8,
        ("Financial District", "Sunset District"): 30,
        ("Financial District", "Chinatown"): 5,
        ("Financial District", "Russian Hill"): 11,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Nob Hill", "Sunset District"): 24,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "North Beach"): 28,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Russian Hill", "North Beach"): 4,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("North Beach", "Haight-Ashbury"): 18
    }

    # Create variables and basic constraints
    meeting_vars = {}
    for friend in friends:
        start = Int(f"start_{friend}")
        end = Int(f"end_{friend}")
        meeting_vars[friend] = (start, end)
        
        data = friends[friend]
        available_start = time_to_minutes(data["available_start"])
        available_end = time_to_minutes(data["available_end"])
        min_duration = data["min_duration"]
        
        s.add(start >= available_start)
        s.add(end <= available_end)
        s.add(end - start >= min_duration)

    # Ordering constraints
    friends_list = list(friends.keys())
    for i in range(len(friends_list)):
        for j in range(i+1, len(friends_list)):
            f1 = friends_list[i]
            f2 = friends_list[j]
            start1, end1 = meeting_vars[f1]
            start2, end2 = meeting_vars[f2]
            loc1 = friends[f1]["location"]
            loc2 = friends[f2]["location"]
            
            # Get travel time
            if (loc1, loc2) in travel_times:
                travel = travel_times[(loc1, loc2)]
            else:
                travel = travel_times[(loc2, loc1)]
            
            # No overlap with travel time
            s.add(Or(
                end1 + travel <= start2,
                end2 + travel <= start1
            ))

    # Starting point constraint
    first_meeting = [meeting_vars[f][0] for f in friends]
    for f in friends:
        loc = friends[f]["location"]
        travel = travel_times[("Union Square", loc)]
        s.add(meeting_vars[f][0] >= travel)

    # Optimization: maximize number of meetings
    meet_flags = [Bool(f"meet_{f}") for f in friends]
    for f in friends:
        start, end = meeting_vars[f]
        s.add(If(meet_flags[friends_list.index(f)], And(start >= 0, end > start), And(start == -1, end == -1)))
    
    s.maximize(Sum([If(flag, 1, 0) for flag in meet_flags]))

    if s.check() == sat:
        model = s.model()
        itinerary = []
        for f in friends:
            start, end = meeting_vars[f]
            start_val = model.evaluate(start).as_long()
            end_val = model.evaluate(end).as_long()
            if start_val >= 0 and end_val > start_val:
                itinerary.append({
                    "action": "meet",
                    "person": f,
                    "start_time": minutes_to_time(start_val),
                    "end_time": minutes_to_time(end_val)
                })
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

solution = solve_scheduling()
print(json.dumps(solution, indent=2))