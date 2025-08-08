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

    # Travel times (symmetric)
    travel_times = {
        "Union Square": {
            "Presidio": 24, "Alamo Square": 15, "Marina District": 18,
            "Financial District": 9, "Nob Hill": 9, "Sunset District": 27,
            "Chinatown": 7, "Russian Hill": 13, "North Beach": 10,
            "Haight-Ashbury": 18
        },
        "Presidio": {
            "Alamo Square": 19, "Marina District": 11, "Financial District": 23,
            "Nob Hill": 18, "Sunset District": 15, "Chinatown": 21,
            "Russian Hill": 14, "North Beach": 18, "Haight-Ashbury": 15
        },
        "Alamo Square": {
            "Marina District": 15, "Financial District": 17, "Nob Hill": 11,
            "Sunset District": 16, "Chinatown": 15, "Russian Hill": 13,
            "North Beach": 15, "Haight-Ashbury": 5
        },
        "Marina District": {
            "Financial District": 17, "Nob Hill": 12, "Sunset District": 19,
            "Chinatown": 15, "Russian Hill": 8, "North Beach": 11,
            "Haight-Ashbury": 16
        },
        "Financial District": {
            "Nob Hill": 8, "Sunset District": 30, "Chinatown": 5,
            "Russian Hill": 11, "North Beach": 7, "Haight-Ashbury": 19
        },
        "Nob Hill": {
            "Sunset District": 24, "Chinatown": 6, "Russian Hill": 5,
            "North Beach": 8, "Haight-Ashbury": 13
        },
        "Sunset District": {
            "Chinatown": 30, "Russian Hill": 24, "North Beach": 28,
            "Haight-Ashbury": 15
        },
        "Chinatown": {
            "Russian Hill": 7, "North Beach": 3, "Haight-Ashbury": 19
        },
        "Russian Hill": {
            "North Beach": 4, "Haight-Ashbury": 17
        },
        "North Beach": {
            "Haight-Ashbury": 18
        }
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
        s.add(start >= 0)  # Can't start before 9:00 AM

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
            if loc1 in travel_times and loc2 in travel_times[loc1]:
                travel = travel_times[loc1][loc2]
            else:
                travel = travel_times[loc2][loc1]
            
            # No overlap with travel time
            s.add(Or(
                end1 + travel <= start2,
                end2 + travel <= start1
            ))

    # Starting point constraint (from Union Square)
    for f in friends:
        loc = friends[f]["location"]
        travel = travel_times["Union Square"][loc]
        s.add(meeting_vars[f][0] >= travel)

    # Optimization: maximize number of meetings and prioritize longer ones
    meet_flags = [Bool(f"meet_{f}") for f in friends]
    for i, f in enumerate(friends):
        start, end = meeting_vars[f]
        s.add(If(meet_flags[i], And(start >= 0, end > start), And(start == -1, end == -1)))
    
    # Weight longer meetings higher
    weights = [friends[f]["min_duration"] for f in friends]
    s.maximize(Sum([If(flag, weight, 0) for flag, weight in zip(meet_flags, weights)]))

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